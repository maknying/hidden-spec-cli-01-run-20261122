// mend — one command-line tool that applies AI-written edits to a tree of
// text files, in four formats: unified diffs, SEARCH/REPLACE blocks, V4A
// patches and JSON text-editor tool calls. Every edit is applied to all of
// its files or to none of them: a failed edit changes nothing, the edits
// after it still run, and when any edit failed no file is written at all.
//
// Node 22, standard library only. Run as:
//   node main.ts [--format=NAME] [--check] [--strict] [PATCH]
// PATCH is a path relative to the working directory, or standard input when
// it is absent or `-`. The working directory is the root of the tree.
//
// When MAKEFUN_ENV_URL is set this file hands the trial over to runner.ts,
// which runs it on each of the trial's checks and posts what it did.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** A fault in the patch itself: exit 2 with this one line. */
class PatchFault extends Error {
  readonly line: string;
  constructor(line: string) {
    super(line);
    this.line = line;
  }
}

/** One edit that could not be applied: exit 1 with `error: <code> <path>`. */
class EditFault extends Error {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    super(`${code} ${path}`);
    this.code = code;
    this.path = path;
  }
}

const isBlank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at `\n`, one trailing `\r` removed from each, and
 *  the empty piece after a final `\n` dropped. */
function splitPatch(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** A path is safe when it is not empty, does not start with `/`, holds no
 *  `\`, and none of its `/`-separated segments is empty, `.` or `..`. */
function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((seg) => seg !== '' && seg !== '.' && seg !== '..');
}

/** Byte order of paths (UTF-8), for the output lines. */
function byteOrder(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

const leadWhitespace = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};
const stripTrailingWs = (s: string): string => s.replace(/[ \t]+$/, '');
const stripBothWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

// ---------------------------------------------------------------------------
// Files as lines
// ---------------------------------------------------------------------------

interface FileText {
  lines: string[];
  br: '\n' | '\r\n';
  eol: boolean;
}

/** Split a file's text into its lines. Its line break is CRLF when its first
 *  line feed follows a carriage return, and LF otherwise. It ends with a line
 *  break when its text ends with that break; an empty file has no lines. */
function readFileText(text: string): FileText {
  if (text === '') return { lines: [], br: '\n', eol: false };
  const nl = text.indexOf('\n');
  const br: '\n' | '\r\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  let eol = false;
  if (text.endsWith(br)) {
    parts.pop();
    eol = true;
  }
  return { lines: parts, br, eol };
}

/** Join a file's lines back, with its own break between them and a final one
 *  exactly when it ended with one. A file of no lines is written empty. */
function writeFileText(f: FileText): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.eol ? f.br : '');
}

// ---------------------------------------------------------------------------
// Matching lines at three tiers
// ---------------------------------------------------------------------------

/** Two lines are equal at a tier: tier 0 exactly; tier 1 once trailing
 *  spaces and tabs are removed from both; tier 2 once leading and trailing
 *  spaces and tabs are removed from both. */
function linesEqual(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripTrailingWs(a) === stripTrailingWs(b);
  return stripBothWs(a) === stripBothWs(b);
}

/** Every position where `old` occurs in `lines` at one tier, starting at
 *  `from`. Occurrences may overlap. */
function occurrencesAt(lines: string[], old: string[], tier: number, from: number): number[] {
  const found: number[] = [];
  if (old.length === 0) return found;
  for (let i = from; i + old.length <= lines.length; i += 1) {
    let ok = true;
    for (let j = 0; j < old.length; j += 1) {
      if (!linesEqual(old[j]!, lines[i + j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) found.push(i);
  }
  return found;
}

interface Found {
  tier: number;
  at: number[];
}

/** The first tier at which `old` occurs at least once, with its positions.
 *  With `strict` only tier 0 is tried. When `eof` is set only occurrences
 *  that end at the file's last line count. */
function findAtFirstTier(
  lines: string[],
  old: string[],
  strict: boolean,
  from: number,
  eof: boolean,
): Found | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    let at = occurrencesAt(lines, old, tier, from);
    if (eof) at = at.filter((p) => p + old.length === lines.length);
    if (at.length > 0) return { tier, at };
  }
  return null;
}

/** The first line at or after `from` equal to a single line at the first tier
 *  where one is. */
function findSingleLine(lines: string[], want: string, strict: boolean, from: number): number | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    for (let i = from; i < lines.length; i += 1) {
      if (linesEqual(want, lines[i]!, tier)) return i;
    }
  }
  return null;
}

interface Replacement {
  oldLines: string[];
  newLines: string[];
  /** new-line index -> old-line index, for context lines. */
  context: Map<number, number>;
}

/** The lines that replace `oldLines` at position `at`. A context line is
 *  written as the file's own matched line, never the patch's. At tier 2 every
 *  other line is re-indented: the leading spaces and tabs of the patch's first
 *  old line are replaced by those of the file's first matched line. At tiers
 *  0 and 1 the new lines are written as they are. */
function renderReplacement(lines: string[], at: number, spec: Replacement, tier: number): string[] {
  const patchLead = leadWhitespace(spec.oldLines[0] ?? '');
  const fileLead = leadWhitespace(lines[at] ?? '');
  return spec.newLines.map((ln, j) => {
    const oldIndex = spec.context.get(j);
    if (oldIndex !== undefined) return lines[at + oldIndex]!;
    if (tier !== 2) return ln;
    if (ln === '' || ln.trim() === '') return ln;
    if (ln.startsWith(patchLead)) return fileLead + ln.slice(patchLead.length);
    return ln;
  });
}

// ---------------------------------------------------------------------------
// The tree as the edits leave it
// ---------------------------------------------------------------------------

/** The tree as the edits leave it: changed paths in `current` (null means
 *  deleted), the rest read from disk. Moves are remembered so the output can
 *  print them as `R <old> -> <new>`. */
class Tree {
  private disk = new Map<string, string | null>();
  readonly current = new Map<string, string | null>();
  readonly moves: Array<{ from: string; to: string }> = [];

  readDisk(p: string): string | null {
    if (!this.disk.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.disk.set(p, v);
    }
    return this.disk.get(p)!;
  }

  get(p: string): string | null {
    return this.current.has(p) ? this.current.get(p)! : this.readDisk(p);
  }
}

type Edit = (tree: Tree) => void;

/** The first of these that holds, where a blank line is one that is empty or
 *  only whitespace: `*** Begin Patch` is v4a, `[` or `{` is json, a
 *  `<<<<<<< SEARCH` line is search-replace, a `diff --git ` line or a `--- `
 *  line followed by a `+++ ` line is unified. Otherwise no format. */
function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (
    lines.some(
      (l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')),
    )
  ) {
    return 'unified';
  }
  return null;
}

// ---------------------------------------------------------------------------
// JSON edits (section 9)
// ---------------------------------------------------------------------------

/** One JSON edit object, or null when the value is not one. A wrong command
 *  or a missing or mistyped key is a parse fault, so it returns null. */
function jsonEditObject(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;

  const existing = (tree: Tree): string => {
    if (!isSafePath(p)) throw new EditFault('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new EditFault('missing', p);
    return t;
  };

  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!isSafePath(p)) throw new EditFault('unsafe', p);
      if (tree.get(p) !== null) throw new EditFault('exists', p);
      tree.current.set(p, text);
    };
  }

  if (
    o.command === 'str_replace' &&
    typeof o.old_str === 'string' &&
    o.old_str !== '' &&
    (o.new_str === undefined || typeof o.new_str === 'string')
  ) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = existing(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      // In a CRLF file the file's text and both strings are read with every
      // `\r\n` as `\n`, and the result is written back with `\r\n`.
      const plain = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = plain(before);
      const old = plain(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new EditFault('no-match', p);
      if (count > 1) throw new EditFault('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + plain(newStr) + t.slice(at + old.length);
      tree.current.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }

  if (
    o.command === 'insert' &&
    typeof o.insert_line === 'number' &&
    Number.isInteger(o.insert_line) &&
    typeof o.new_str === 'string'
  ) {
    const line = o.insert_line;
    const added = splitPatch(o.new_str);
    return (tree) => {
      const before = existing(tree);
      const nl = before.indexOf('\n');
      const br: '\n' | '\r\n' = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const parts = before === '' ? [] : before.split(br);
      const endsWithBreak = before !== '' && before.endsWith(br);
      if (endsWithBreak) parts.pop();
      if (line < 0 || line > parts.length) throw new EditFault('no-match', p);
      parts.splice(line, 0, ...added);
      tree.current.set(p, parts.length === 0 ? '' : parts.join(br) + (endsWithBreak ? br : ''));
    };
  }

  return null;
}

/** Read a JSON patch: either one JSON array of edit objects, or JSON Lines
 *  with one edit object a line and blank lines ignored. In array form any
 *  fault is a parse fault at the line where the array starts; in JSON Lines
 *  form a line that does not hold one valid edit object is a parse fault at
 *  that line. */
function parseJsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new PatchFault('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new PatchFault(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new PatchFault(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEditObject(x);
      if (e === null) throw new PatchFault(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (isBlank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEditObject(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new PatchFault(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------------------------------------------------------------------------
// Unified diffs (section 6)
// ---------------------------------------------------------------------------

interface Hunk {
  start: number;
  oldLines: string[];
  newLines: string[];
  context: Map<number, number>;
  /** The `+` lines of the hunk, in order (for creations). */
  plusLines: string[];
  /** A `\` line follows the hunk's last context or `+` line. */
  noEol: boolean;
  /** A `\` line follows the hunk's last `+` line. */
  plusNoEol: boolean;
}

interface UnifiedSection {
  oldPath: string | null;
  newPath: string | null;
  newFile: boolean;
  deletedFile: boolean;
  /** A `--- `/`+++ ` pair has already named this section's paths. */
  sawPair: boolean;
  hunks: Hunk[];
}

/** The path a `--- ` or `+++ ` line names: the text after the four
 *  characters, up to the first tab, with surrounding spaces removed, and a
 *  leading `a/` or `b/` removed. */
function headerPath(line: string): string {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

const isHunkBodyLine = (l: string): boolean =>
  l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+' || l[0] === '\\';

/** Read the unified diff: its sections, their headers and their hunks. */
function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: UnifiedSection[] = [];
  const freshSection = (): UnifiedSection => ({
    oldPath: null,
    newPath: null,
    newFile: false,
    deletedFile: false,
    sawPair: false,
    hunks: [],
  });
  let cur: UnifiedSection | null = null;
  const n = lines.length;
  let i = 0;
  while (i < n) {
    const line = lines[i]!;

    if (line.startsWith('diff --git ')) {
      const m = line.match(/^diff --git a\/(.+) b\/(.+)$/);
      if (m === null) throw new PatchFault(`error: parse ${i + 1}`);
      cur = freshSection();
      cur.oldPath = m[1] === '/dev/null' ? null : m[1]!;
      cur.newPath = m[2] === '/dev/null' ? null : m[2]!;
      sections.push(cur);
      i += 1;
      continue;
    }

    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const oldP = headerPath(line);
      const newP = headerPath(lines[i + 1]!);
      // A `--- `/`+++ ` pair is part of the current section's header while
      // that header is still open and has no pair yet; otherwise it starts
      // a new section. A section's header is open until its first hunk.
      if (cur !== null && cur.hunks.length === 0 && !cur.sawPair) {
        cur.oldPath = oldP === '/dev/null' ? null : oldP;
        cur.newPath = newP === '/dev/null' ? null : newP;
        cur.sawPair = true;
      } else {
        cur = freshSection();
        cur.oldPath = oldP === '/dev/null' ? null : oldP;
        cur.newPath = newP === '/dev/null' ? null : newP;
        cur.sawPair = true;
        sections.push(cur);
      }
      i += 2;
      continue;
    }

    if (cur !== null && cur.hunks.length === 0 && line.startsWith('--- ')) {
      // A `--- ` line not followed by a `+++ ` line, inside a section's
      // header, is a parse fault at the line after it.
      throw new PatchFault(`error: parse ${i + 2}`);
    }

    if (line.startsWith('@@')) {
      if (cur === null) throw new PatchFault(`error: parse ${i + 1}`);
      const m = line.match(/^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/);
      if (m === null) throw new PatchFault(`error: parse ${i + 1}`);
      const start = Number(m[1]);
      const body: string[] = [];
      let j = i + 1;
      while (j < n) {
        const l = lines[j]!;
        if (l.startsWith('diff --git ')) break;
        if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (!isHunkBodyLine(l)) break;
        body.push(l);
        j += 1;
      }
      // Empty lines at the end of a body are not part of it.
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      const oldLines: string[] = [];
      const newLines: string[] = [];
      const plusLines: string[] = [];
      const context = new Map<number, number>();
      let lastContextOrPlus = -1;
      let lastPlus = -1;
      for (let k = 0; k < body.length; k += 1) {
        const b = body[k]!;
        const c = b[0]!;
        if (c === ' ' || b === '') {
          // A context line; an empty line is a context line whose text is
          // empty.
          context.set(newLines.length, oldLines.length);
          oldLines.push(b === '' ? '' : b.slice(1));
          newLines.push(b === '' ? '' : b.slice(1));
          lastContextOrPlus = k;
        } else if (c === '-') {
          oldLines.push(b.slice(1));
        } else if (c === '+') {
          newLines.push(b.slice(1));
          plusLines.push(b.slice(1));
          lastContextOrPlus = k;
          lastPlus = k;
        }
        // A `\` line refers to the body line before it; it is not a line
        // of the old or new text.
      }
      const noEol =
        lastContextOrPlus >= 0 && lastContextOrPlus + 1 < body.length && body[lastContextOrPlus + 1]![0] === '\\';
      const plusNoEol =
        lastPlus >= 0 && lastPlus + 1 < body.length && body[lastPlus + 1]![0] === '\\';
      cur.hunks.push({ start, oldLines, newLines, context, plusLines, noEol, plusNoEol });
      i = j;
      continue;
    }

    if (cur !== null && cur.hunks.length === 0) {
      if (line.startsWith('rename from ')) {
        if (!cur.sawPair) {
          const p = line.slice('rename from '.length).trim();
          cur.oldPath = p === '/dev/null' ? null : p;
        }
      } else if (line.startsWith('rename to ')) {
        if (!cur.sawPair) {
          const p = line.slice('rename to '.length).trim();
          cur.newPath = p === '/dev/null' ? null : p;
        }
      } else if (line.startsWith('new file mode')) {
        cur.newFile = true;
      } else if (line.startsWith('deleted file mode')) {
        cur.deletedFile = true;
      }
      // `index`, `old mode`, `new mode`, `similarity index`,
      // `dissimilarity index` and `Index:` lines, and any other line, are
      // ignored.
      i += 1;
      continue;
    }

    // Outside bodies, lines that are not part of a section header are
    // ignored (prose, code fences).
    i += 1;
  }
  return sections.map((sec) => unifiedSectionEdit(sec, strict));
}

/** Apply a section's hunks in order, each to the result of the ones before
 *  it. When the old lines are not empty the hunk takes the occurrence at the
 *  tier where they are found whose position is nearest to A - 1 + d, the
 *  earlier of two equally near; when they are empty the new lines are
 *  inserted after the first A + d lines. */
function applyHunks(text: string, hunks: Hunk[], strict: boolean, path: string): string {
  const file = readFileText(text);
  let d = 0;
  for (const h of hunks) {
    if (h.oldLines.length > 0) {
      const found = findAtFirstTier(file.lines, h.oldLines, strict, 0, false);
      if (found === null) throw new EditFault('no-match', path);
      const target = h.start - 1 + d;
      let best = found.at[0]!;
      for (const p of found.at) {
        if (Math.abs(p - target) < Math.abs(best - target)) best = p;
      }
      const repl = renderReplacement(file.lines, best, h, found.tier);
      const atEof = best + h.oldLines.length === file.lines.length;
      file.lines.splice(best, h.oldLines.length, ...repl);
      if (atEof) file.eol = !h.noEol;
      d += h.newLines.length - h.oldLines.length;
    } else {
      const pos = Math.max(0, Math.min(h.start + d, file.lines.length));
      const atEnd = pos === file.lines.length;
      file.lines.splice(pos, 0, ...h.newLines);
      if (atEnd) file.eol = !h.noEol;
      d += h.newLines.length;
    }
  }
  return writeFileText(file);
}

/** One unified section is one edit: a creation, a deletion, a move, or a
 *  change of one path. */
function unifiedSectionEdit(sec: UnifiedSection, strict: boolean): Edit {
  return (tree) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    const creating = oldP === null || sec.newFile;
    if (creating) {
      if (newP === null) throw new EditFault('unsafe', '/dev/null');
      if (!isSafePath(newP)) throw new EditFault('unsafe', newP);
      if (tree.get(newP) !== null) throw new EditFault('exists', newP);
      const plus: string[] = [];
      let noEol = false;
      for (const h of sec.hunks) {
        plus.push(...h.plusLines);
        if (h.plusLines.length > 0) noEol = h.plusNoEol;
      }
      tree.current.set(newP, plus.length === 0 ? '' : plus.join('\n') + (noEol ? '' : '\n'));
      return;
    }
    const deleting = newP === null || sec.deletedFile;
    if (deleting) {
      if (oldP === null) throw new EditFault('unsafe', '/dev/null');
      if (!isSafePath(oldP)) throw new EditFault('unsafe', oldP);
      if (tree.get(oldP) === null) throw new EditFault('missing', oldP);
      tree.current.set(oldP, null);
      return;
    }
    // Both paths are named and differ or not: a move or a change.
    if (!isSafePath(oldP!)) throw new EditFault('unsafe', oldP!);
    if (!isSafePath(newP!)) throw new EditFault('unsafe', newP!);
    const before = tree.get(oldP!);
    if (before === null) throw new EditFault('missing', oldP!);
    if (oldP !== newP) {
      if (tree.get(newP!) !== null) throw new EditFault('exists', newP!);
      const after = applyHunks(before, sec.hunks, strict, oldP!);
      tree.current.set(newP!, after);
      tree.current.set(oldP!, null);
      tree.moves.push({ from: oldP!, to: newP! });
    } else {
      tree.current.set(oldP!, applyHunks(before, sec.hunks, strict, oldP!));
    }
  };
}

// ---------------------------------------------------------------------------
// SEARCH/REPLACE blocks (section 7)
// ---------------------------------------------------------------------------

interface SearchBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

/** Read the SEARCH/REPLACE blocks. The path is the nearest line before the
 *  `<<<<<<< SEARCH` line, and after the previous block's `>>>>>>> REPLACE`
 *  line (or the start of the patch), that is not blank and does not start
 *  with three backticks; when there is no such line the block takes the
 *  previous block's path. Lines outside blocks are otherwise ignored. */
function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  const n = lines.length;
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < n) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let j = i - 1; j > prevEnd; j -= 1) {
      const l = lines[j]!;
      if (isBlank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new PatchFault(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    let eq = -1;
    let rep = -1;
    for (let j = i + 1; j < n; j += 1) {
      const l = lines[j]!.trimEnd();
      if (l === '<<<<<<< SEARCH') break;
      if (eq === -1 && l === '=======') {
        eq = j;
        continue;
      }
      if (l === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (eq === -1 || rep === -1) throw new PatchFault(`error: parse ${searchLine + 1}`);
    const block: SearchBlock = {
      path,
      oldLines: lines.slice(i + 1, eq),
      newLines: lines.slice(eq + 1, rep),
    };
    edits.push(searchBlockEdit(block, strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

/** One block is one edit. With empty old lines the file is created with the
 *  new lines; otherwise the file exists and the old lines occur at their tier
 *  exactly once, and the new lines replace them. */
function searchBlockEdit(block: SearchBlock, strict: boolean): Edit {
  return (tree) => {
    const p = block.path;
    if (!isSafePath(p)) throw new EditFault('unsafe', p);
    if (block.oldLines.length === 0) {
      if (tree.get(p) !== null) throw new EditFault('exists', p);
      tree.current.set(p, block.newLines.length === 0 ? '' : block.newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(p);
    if (before === null) throw new EditFault('missing', p);
    const file = readFileText(before);
    const found = findAtFirstTier(file.lines, block.oldLines, strict, 0, false);
    if (found === null) throw new EditFault('no-match', p);
    if (found.at.length > 1) throw new EditFault('ambiguous', p);
    const pos = found.at[0]!;
    const repl = renderReplacement(
      file.lines,
      pos,
      { oldLines: block.oldLines, newLines: block.newLines, context: new Map() },
      found.tier,
    );
    file.lines.splice(pos, block.oldLines.length, ...repl);
    tree.current.set(p, writeFileText(file));
  };
}

// ---------------------------------------------------------------------------
// V4A patches (section 8)
// ---------------------------------------------------------------------------

interface V4aChunk {
  anchor: string;
  /** The chunk's raw body lines, before trailing blanks are dropped. */
  body: string[];
  oldLines: string[];
  newLines: string[];
  context: Map<number, number>;
  eof: boolean;
}

const isV4aBodyLine = (l: string): boolean => l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+';

/** A chunk's body lines, turned into its old lines (context and `-` lines)
 *  and new lines (context and `+` lines). */
function v4aChunkLines(body: string[]): { oldLines: string[]; newLines: string[]; context: Map<number, number> } {
  const oldLines: string[] = [];
  const newLines: string[] = [];
  const context = new Map<number, number>();
  for (const b of body) {
    const c = b[0];
    if (c === ' ' || b === '') {
      context.set(newLines.length, oldLines.length);
      oldLines.push(b === '' ? '' : b.slice(1));
      newLines.push(b === '' ? '' : b.slice(1));
    } else if (c === '-') {
      oldLines.push(b.slice(1));
    } else if (c === '+') {
      newLines.push(b.slice(1));
    }
  }
  return { oldLines, newLines, context };
}

/** Read one chunk's body lines, starting at `i`. The body ends at an `@@`
 *  line, a section header, `*** End of File`, `*** End Patch`, or any line
 *  that is not a body line. A `*** End of File` line ends the chunk and
 *  anchors it to the end of the file. */
function readV4aChunkBody(
  lines: string[],
  i: number,
  last: number,
): { body: string[]; eof: boolean; next: number } {
  const body: string[] = [];
  let j = i;
  while (j < last) {
    if (!isV4aBodyLine(lines[j]!)) break;
    body.push(lines[j]!);
    j += 1;
  }
  let eof = false;
  if (j < last && lines[j] === '*** End of File') {
    eof = true;
    j += 1;
  }
  return { body, eof, next: j };
}

/** Read a V4A patch. The first non-blank line is `*** Begin Patch` and the
 *  last non-blank line is `*** End Patch`, both compared with their
 *  surrounding whitespace removed. Blank lines at the end of a section are
 *  not part of it; blank lines between sections are ignored. */
function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new PatchFault('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new PatchFault(`error: parse ${first + 1}`);
  const last = lines.length - 1 - [...lines].reverse().findIndex((l) => !isBlank(l));
  if (lines[last]!.trim() !== '*** End Patch') throw new PatchFault(`error: parse ${lines.length + 1}`);

  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (isBlank(line)) {
      i += 1;
      continue;
    }
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice('*** Add File: '.length).trim();
      i += 1;
      const fileLines: string[] = [];
      while (i < last) {
        const l = lines[i]!;
        if (l === '') {
          fileLines.push('');
          i += 1;
        } else if (l.startsWith('+')) {
          fileLines.push(l.slice(1));
          i += 1;
        } else {
          break;
        }
      }
      while (fileLines.length > 0 && fileLines[fileLines.length - 1] === '') fileLines.pop();
      edits.push((tree) => {
        if (!isSafePath(path)) throw new EditFault('unsafe', path);
        if (tree.get(path) !== null) throw new EditFault('exists', path);
        tree.current.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice('*** Delete File: '.length).trim();
      i += 1;
      edits.push((tree) => {
        if (!isSafePath(path)) throw new EditFault('unsafe', path);
        if (tree.get(path) === null) throw new EditFault('missing', path);
        tree.current.set(path, null);
      });
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const path = line.slice('*** Update File: '.length).trim();
      const updateLine = i;
      i += 1;
      let moveTo: string | null = null;
      if (i < last && lines[i]!.startsWith('*** Move to: ')) {
        moveTo = lines[i]!.slice('*** Move to: '.length).trim();
        i += 1;
      }
      const chunks: V4aChunk[] = [];
      let firstChunk = true;
      let lastEndedByEof = false;
      // The line the chunk loop stopped at, when it stopped on a line that
      // is not a section header and not the end of the patch.
      let stoppedAt: number | null = null;
      while (i < last) {
        const l = lines[i]!;
        if (l.startsWith('@@')) {
          const anchor = l.slice(2).trim();
          i += 1;
          const parsed = readV4aChunkBody(lines, i, last);
          i = parsed.next;
          chunks.push({ anchor, body: parsed.body, oldLines: [], newLines: [], context: new Map(), eof: parsed.eof });
          lastEndedByEof = parsed.eof;
          firstChunk = false;
        } else if (firstChunk && isV4aBodyLine(l)) {
          const parsed = readV4aChunkBody(lines, i, last);
          i = parsed.next;
          chunks.push({ anchor: '', body: parsed.body, oldLines: [], newLines: [], context: new Map(), eof: parsed.eof });
          lastEndedByEof = parsed.eof;
          firstChunk = false;
        } else if (isBlank(l)) {
          // A blank line between chunks, or at the end of the section, is
          // not part of any chunk.
          i += 1;
        } else {
          stoppedAt = i;
          break;
        }
      }
      // Blank lines at the end of a section are not part of it: drop them
      // from the last chunk, unless that chunk ended at `*** End of File`
      // (then its blank lines sit before that line, not at the section's
      // end, and stay).
      if (chunks.length > 0 && !lastEndedByEof) {
        const tail = chunks[chunks.length - 1]!;
        while (tail.body.length > 0 && isBlank(tail.body[tail.body.length - 1]!)) tail.body.pop();
      }
      for (const ch of chunks) {
        const { oldLines, newLines, context } = v4aChunkLines(ch.body);
        ch.oldLines = oldLines;
        ch.newLines = newLines;
        ch.context = context;
      }
      if (chunks.length === 0 && moveTo === null) {
        // An Update File section with no chunk and no `*** Move to:` is a
        // parse fault at its Update File line — unless the section stopped
        // on a line that is itself not part of the grammar, which is a
        // parse fault at that line.
        if (
          stoppedAt !== null &&
          !lines[stoppedAt]!.startsWith('*** Add File: ') &&
          !lines[stoppedAt]!.startsWith('*** Delete File: ') &&
          !lines[stoppedAt]!.startsWith('*** Update File: ')
        ) {
          throw new PatchFault(`error: parse ${stoppedAt + 1}`);
        }
        throw new PatchFault(`error: parse ${updateLine + 1}`);
      }
      edits.push(v4aUpdateEdit(path, moveTo, chunks, strict));
      continue;
    }
    throw new PatchFault(`error: parse ${i + 1}`);
  }
  return edits;
}

/** One Update File section is one edit. The chunks apply in order, with a
 *  cursor that starts at line 0. A chunk with an anchor first finds the first
 *  line at or after the cursor equal to the anchor, and the cursor moves past
 *  it; the chunk then takes the first occurrence of its old lines at or after
 *  the cursor, and the cursor moves to just after the lines written. */
function v4aUpdateEdit(path: string, moveTo: string | null, chunks: V4aChunk[], strict: boolean): Edit {
  return (tree) => {
    if (!isSafePath(path)) throw new EditFault('unsafe', path);
    if (moveTo !== null && !isSafePath(moveTo)) throw new EditFault('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new EditFault('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new EditFault('exists', moveTo);
    const file = readFileText(before);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== '') {
        const at = findSingleLine(file.lines, ch.anchor, strict, cursor);
        if (at === null) throw new EditFault('no-match', path);
        cursor = at + 1;
      }
      if (ch.oldLines.length > 0) {
        const found = findAtFirstTier(file.lines, ch.oldLines, strict, cursor, ch.eof);
        if (found === null) throw new EditFault('no-match', path);
        const pos = found.at[0]!;
        const repl = renderReplacement(file.lines, pos, ch, found.tier);
        file.lines.splice(pos, ch.oldLines.length, ...repl);
        cursor = pos + repl.length;
      } else {
        const pos = ch.eof ? file.lines.length : cursor;
        file.lines.splice(pos, 0, ...ch.newLines);
        cursor = pos + ch.newLines.length;
      }
    }
    const after = writeFileText(file);
    if (moveTo !== null) {
      tree.current.set(moveTo, after);
      tree.current.set(path, null);
      tree.moves.push({ from: path, to: moveTo });
    } else {
      tree.current.set(path, after);
    }
  };
}

// ---------------------------------------------------------------------------
// Order and atomicity (section 10), output and exit codes (section 2)
// ---------------------------------------------------------------------------

/** Run the CLI on its arguments. Returns the exit code and the lines for
 *  standard output, each ended by a line feed and nothing else. */
function run(argv: string[]): { code: number; out: string[] } {
  // The command line: options and PATCH may come in any order, and `--`
  // ends the options. A usage error is an argument that starts with `-`
  // and is not `-` and not one of the options above (before `--`), an
  // option given twice, a `--format` value other than the five names, or
  // more than one positional argument.
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of argv) {
    if (!ended && a === '--') {
      ended = true;
    } else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice('--format='.length))) {
        format = a.slice('--format='.length);
      } else if (a === '--check' && !check) {
        check = true;
      } else if (a === '--strict' && !strict) {
        strict = true;
      } else {
        return { code: 2, out: ['error: usage'] };
      }
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };

  // PATCH is the path of the patch file, relative to the working directory.
  // When PATCH is absent or is `-`, the patch is read from standard input.
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = splitPatch(text);

  // The format is detected, or named; a named format is read as that format
  // whatever the text holds. A usage error wins over everything, and a parse
  // error is reported before any file is looked at.
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = parseJsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new PatchFault('error: parse 1');
  } catch (e) {
    if (e instanceof PatchFault) return { code: 2, out: [e.line] };
    throw e;
  }

  // Edits apply in the patch's order to the tree as earlier edits left it.
  // A failed edit changes nothing, and the edits after it still run, so
  // every failure is reported. When any edit failed, no file is written.
  const tree = new Tree();
  const fails: EditFault[] = [];
  for (const edit of edits) {
    const beforeNow = new Map(tree.current);
    const beforeMoves = [...tree.moves];
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof EditFault)) throw e;
      tree.current.clear();
      for (const [k, v] of beforeNow) tree.current.set(k, v);
      tree.moves.length = 0;
      tree.moves.push(...beforeMoves);
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }

  // One line for each path whose state changed, in byte order of the paths.
  // A file moved by a move edit prints `R <old> -> <new>` instead of that
  // pair's `D` and `A` lines, and sorts by `<new>`.
  interface Row {
    key: string;
    line: string;
    /** For a move, the old path to delete once the new file is written. */
    del?: string;
  }
  const rows: Row[] = [];
  for (const p of [...tree.current.keys()].sort(byteOrder)) {
    const was = tree.readDisk(p);
    const now = tree.current.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const mv of tree.moves) {
    if (
      tree.readDisk(mv.from) !== null &&
      tree.get(mv.from) === null &&
      tree.readDisk(mv.to) === null &&
      tree.get(mv.to) !== null
    ) {
      const d = rows.findIndex((r) => r.key === mv.from && r.line.startsWith('D '));
      const a = rows.findIndex((r) => r.key === mv.to && r.line.startsWith('A '));
      if (d >= 0 && a >= 0) {
        rows.splice(Math.max(d, a), 1);
        rows.splice(Math.min(d, a), 1);
        rows.push({ key: mv.to, line: `R ${mv.from} -> ${mv.to}`, del: mv.from });
      }
    }
  }
  rows.sort((a, b) => byteOrder(a.key, b.key));

  if (!check) {
    for (const row of rows) {
      const p = row.key;
      const now = tree.current.get(p)!;
      if (row.line.startsWith('D ')) {
        rmSync(p, { force: true });
      } else if (now !== null) {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
        if (row.del !== undefined) rmSync(row.del, { force: true });
      }
    }
  }
  const out = rows.map((r) => r.line);
  out.push(`ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`);
  return { code: 0, out };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this
  // file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
