// main.ts is mend, the CLI SPEC.md specifies (MIT). It reads a patch in one of four formats (unified diff,
// SEARCH/REPLACE blocks, V4A, JSON edits), finds the lines each edit names at the first of three matching tiers,
// and writes every change or none, printing what changed or why each edit failed. SPEC.md is the whole contract;
// this file follows it section by section. Node 22, the standard library alone; run as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to
// runner.ts (the last lines below): that hand-over and runner.ts are the kit's, kept as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

/** A patch's lines (section 3): split at \n, one trailing \r removed, no empty piece after a final \n. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** A safe path (section 3). */
function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file as its lines, its own line break and whether it ends with one (section 3). */
interface FileModel {
  lines: string[];
  br: '\n' | '\r\n';
  final: boolean;
}

function parseFile(text: string): FileModel {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  let final = false;
  if (text.endsWith(br)) {
    final = true;
    lines.pop();
  }
  return { lines, br, final };
}

function serialize(m: FileModel): string {
  if (m.lines.length === 0) return '';
  return m.lines.join(m.br) + (m.final ? m.br : '');
}

/** A file an edit creates: LF breaks, a final one exactly when `final` says so (section 3). */
function serializeCreated(lines: string[], final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join('\n') + (final ? '\n' : '');
}

// Section 5: matching lines at three tiers.

const trimTrail = (s: string): string => s.replace(/[ \t]+$/, '');
const trimBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadingWS = (s: string): string => /^[ \t]*/.exec(s)![0]!;

function tierEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trimTrail(a) === trimTrail(b);
  return trimBoth(a) === trimBoth(b);
}

function findOccurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  for (let i = 0; i + o.length <= lines.length; i += 1) {
    let ok = true;
    for (let k = 0; k < o.length; k += 1) {
      if (!tierEq(lines[i + k]!, o[k]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which O occurs in lines, and its occurrence positions there; null when it occurs nowhere. */
function findTier(lines: string[], o: string[], strict: boolean): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const positions = findOccurrences(lines, o, t);
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

/** The same, with occurrences restricted to those starting at or after `from` (and, for an end-of-file chunk, ending at the last line). */
function findTierFrom(
  lines: string[],
  o: string[],
  strict: boolean,
  from: number,
  eofOnly: boolean,
): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const positions = findOccurrences(lines, o, t).filter((p) => p >= from && (!eofOnly || p + o.length === lines.length));
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

type LineKind = 'ctx' | 'minus' | 'plus';
interface OLine {
  kind: LineKind;
  text: string;
}

/**
 * The lines that replace the matched ones (section 5): a context line is written as the file's own matched line;
 * at tier 2 every other line is re-indented, its O-first-line prefix P replaced by the file's F where it starts with P.
 */
function buildReplacement(fileLines: string[], pos: number, o: OLine[], n: OLine[], tier: number): string[] {
  const f = leadingWS(fileLines[pos]!);
  const p = leadingWS(o[0]!.text);
  const out: string[] = [];
  let oi = 0;
  for (const ne of n) {
    if (ne.kind === 'ctx') {
      while (o[oi]!.kind === 'minus') oi += 1;
      out.push(fileLines[pos + oi]!);
      oi += 1;
    } else {
      let t = ne.text;
      if (tier === 2 && t !== '' && !/^[ \t]+$/.test(t) && t.startsWith(p)) t = f + t.slice(p.length);
      out.push(t);
    }
  }
  return out;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk; `moves` records each successful move edit. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: [string, string][] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** Format detection (section 4). */
function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const m = parseFile(before);
      if (line < 0 || line > m.lines.length) throw new Fail('no-match', p);
      m.lines.splice(line, 0, ...add);
      tree.now.set(p, serialize(m));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// Section 6: unified diffs.

interface BodyLine {
  kind: LineKind | 'bs';
  text: string;
  emptyLine: boolean; // the body line was a truly empty patch line (a context line whose text is empty)
}

interface Hunk {
  a: number;
  body: BodyLine[];
}

interface USection {
  gitOld: string | undefined;
  gitNew: string | undefined;
  hasPair: boolean;
  pairOld: string | null | undefined; // null: /dev/null
  pairNew: string | null | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  newFile: boolean;
  delFile: boolean;
  hunks: Hunk[];
}

/** The path a --- or +++ line names: after the four characters, up to the first tab, surrounding spaces removed, a/ or b/ removed. */
function headerPath(line: string): string | null {
  const t = line.slice(4).split('\t')[0]!.trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/') || t.startsWith('b/')) return t.slice(2);
  return t;
}

const HUNK_RE = /^@@ -(\d+)(?:,\d+)? \+\d+(?:,\d+)? @@/;

/** Read one hunk whose header is at index hi into the section; returns the index of the first line after its body. */
function readHunk(lines: string[], hi: number, a: number, sec: USection): number {
  const body: BodyLine[] = [];
  let j = hi + 1;
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (l === '') body.push({ kind: 'ctx', text: '', emptyLine: true });
    else if (l[0] === ' ') body.push({ kind: 'ctx', text: l.slice(1), emptyLine: false });
    else if (l[0] === '-') body.push({ kind: 'minus', text: l.slice(1), emptyLine: false });
    else if (l[0] === '+') body.push({ kind: 'plus', text: l.slice(1), emptyLine: false });
    else if (l[0] === '\\') body.push({ kind: 'bs', text: l.slice(1), emptyLine: false });
    else break;
    j += 1;
  }
  while (body.length > 0 && body[body.length - 1]!.emptyLine) body.pop();
  sec.hunks.push({ a, body });
  return j;
}

/** Whether a \ line follows the hunk's last context or + line. */
function bsAfterLastNew(body: BodyLine[]): boolean {
  for (let k = body.length - 1; k >= 0; k -= 1) {
    const b = body[k]!;
    if (b.kind === 'ctx' || b.kind === 'plus') return body[k + 1]?.kind === 'bs';
  }
  return false;
}

/** Apply a section's hunks in order to the file model; a hunk that finds nothing fails the section with no-match. */
function applyHunks(model: FileModel, hunks: Hunk[], strict: boolean, path: string): void {
  let d = 0;
  for (const h of hunks) {
    const o: OLine[] = [];
    const n: OLine[] = [];
    for (const b of h.body) {
      if (b.kind === 'ctx') {
        o.push({ kind: 'ctx', text: b.text });
        n.push({ kind: 'ctx', text: b.text });
      } else if (b.kind === 'minus') o.push({ kind: 'minus', text: b.text });
      else if (b.kind === 'plus') n.push({ kind: 'plus', text: b.text });
    }
    const bs = bsAfterLastNew(h.body);
    if (o.length === 0) {
      const pos = Math.max(0, Math.min(h.a + d, model.lines.length));
      const atEnd = pos === model.lines.length;
      model.lines.splice(pos, 0, ...n.map((e) => e.text));
      if (atEnd) model.final = !bs;
      d += n.length;
    } else {
      const found = findTier(model.lines, o.map((e) => e.text), strict);
      if (found === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let pos = found.positions[0]!;
      for (const p of found.positions) {
        if (Math.abs(p - target) < Math.abs(pos - target)) pos = p;
      }
      const repl = buildReplacement(model.lines, pos, o, n, found.tier);
      const atEnd = pos + o.length === model.lines.length;
      model.lines.splice(pos, o.length, ...repl);
      if (atEnd) model.final = !bs;
      d += n.length - o.length;
    }
  }
}

/** The one edit a unified section is. */
function sectionEdit(s: USection, strict: boolean): Edit {
  const oldPath = s.hasPair ? s.pairOld : s.renameFrom !== undefined ? s.renameFrom : s.gitOld;
  const newPath = s.hasPair ? s.pairNew : s.renameTo !== undefined ? s.renameTo : s.gitNew;
  const isCreate = s.newFile || oldPath === null;
  const isDelete = s.delFile || newPath === null;
  return (tree) => {
    if (isCreate) {
      const p = (newPath ?? '') as string;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      const out: string[] = [];
      let lastBody: BodyLine[] | null = null;
      let lastIdx = -1;
      for (const h of s.hunks) {
        h.body.forEach((b, idx) => {
          if (b.kind === 'plus') {
            out.push(b.text);
            lastBody = h.body;
            lastIdx = idx;
          }
        });
      }
      let final = true;
      if (lastBody !== null && (lastBody as BodyLine[])[lastIdx + 1]?.kind === 'bs') final = false;
      tree.now.set(p, serializeCreated(out, final));
      return;
    }
    if (isDelete) {
      const p = (oldPath ?? '') as string;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return;
    }
    const o = (oldPath ?? '') as string;
    const nw = (newPath ?? '') as string;
    if (!safe(o)) throw new Fail('unsafe', o);
    if (!safe(nw)) throw new Fail('unsafe', nw);
    const text = tree.get(o);
    if (text === null) throw new Fail('missing', o);
    const move = o !== nw;
    if (move && tree.get(nw) !== null) throw new Fail('exists', nw);
    const model = parseFile(text);
    applyHunks(model, s.hunks, strict, o);
    const result = serialize(model);
    if (move) {
      tree.now.set(o, null);
      tree.now.set(nw, result);
      tree.moves.push([o, nw]);
    } else {
      tree.now.set(o, result);
    }
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: USection[] = [];
  let cur: USection | null = null;
  let inHeader = false;
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.+) b\/(.+)$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = { gitOld: m[1]!, gitNew: m[2]!, hasPair: false, pairOld: undefined, pairNew: undefined, renameFrom: undefined, renameTo: undefined, newFile: false, delFile: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      i += 1;
      continue;
    }
    if (inHeader && cur !== null) {
      if (line.startsWith('--- ')) {
        const next = lines[i + 1];
        if (next === undefined || !next.startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
        cur.pairOld = headerPath(line);
        cur.pairNew = headerPath(next);
        cur.hasPair = true;
        i += 2;
        continue;
      }
      if (line.startsWith('rename from ')) {
        cur.renameFrom = line.slice(12);
        i += 1;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renameTo = line.slice(10);
        i += 1;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.newFile = true;
        i += 1;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.delFile = true;
        i += 1;
        continue;
      }
      if (line.startsWith('@@')) {
        const m = HUNK_RE.exec(line);
        if (m === null) throw new Exit2(`error: parse ${i + 1}`);
        i = readHunk(lines, i, parseInt(m[1]!, 10), cur);
        inHeader = false;
        continue;
      }
      i += 1; // any other header line is ignored
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      cur = { gitOld: undefined, gitNew: undefined, hasPair: true, pairOld: headerPath(line), pairNew: headerPath(lines[i + 1]!), renameFrom: undefined, renameTo: undefined, newFile: false, delFile: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      i += 2;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = HUNK_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      i = readHunk(lines, i, parseInt(m[1]!, 10), cur);
      continue;
    }
    i += 1; // prose and anything else outside bodies is ignored
  }
  return sections.map((s) => sectionEdit(s, strict));
}

// Section 7: SEARCH/REPLACE blocks.

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, serializeCreated(newLines, true));
      return;
    }
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    const model = parseFile(text);
    const found = findTier(model.lines, oldLines, strict);
    if (found === null) throw new Fail('no-match', path);
    if (found.positions.length > 1) throw new Fail('ambiguous', path);
    const pos = found.positions[0]!;
    const repl = buildReplacement(
      model.lines,
      pos,
      oldLines.map((t) => ({ kind: 'plus' as LineKind, text: t })),
      newLines.map((t) => ({ kind: 'plus' as LineKind, text: t })),
      found.tier,
    );
    model.lines.splice(pos, oldLines.length, ...repl);
    tree.now.set(path, serialize(model));
  };
}

function srEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchIdx = i;
    let path: string | null = null;
    for (let k = searchIdx - 1; k >= prevEnd; k -= 1) {
      const l = lines[k]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = prevPath;
    }
    let j = searchIdx + 1;
    while (j < lines.length && lines[j]!.trimEnd() !== '=======') j += 1;
    if (j >= lines.length) throw new Exit2(`error: parse ${searchIdx + 1}`);
    let k = j + 1;
    while (k < lines.length && lines[k]!.trimEnd() !== '>>>>>>> REPLACE') k += 1;
    if (k >= lines.length) throw new Exit2(`error: parse ${searchIdx + 1}`);
    edits.push(srEdit(path, lines.slice(searchIdx + 1, j), lines.slice(j + 1, k), strict));
    prevPath = path;
    prevEnd = k + 1;
    i = k + 1;
  }
  return edits;
}

// Section 8: V4A patches.

interface VChunk {
  anchor: string | null;
  eof: boolean;
  body: OLine[];
}

const isVBodyLine = (t: string): boolean => t === '' || t[0] === ' ' || t[0] === '-' || t[0] === '+';

/** Collect body lines into the chunk from content index idx; returns the first index not collected. */
function readVBody(content: { line: number; text: string }[], idx: number, chunk: VChunk): number {
  while (idx < content.length) {
    const t = content[idx]!.text;
    if (t === '') chunk.body.push({ kind: 'ctx', text: '' });
    else if (t[0] === ' ') chunk.body.push({ kind: 'ctx', text: t.slice(1) });
    else if (t[0] === '-') chunk.body.push({ kind: 'minus', text: t.slice(1) });
    else if (t[0] === '+') chunk.body.push({ kind: 'plus', text: t.slice(1) });
    else break;
    idx += 1;
  }
  return idx;
}

/** Parse one V4A section's content into its edit; structural faults are parse errors, thrown here. */
function v4aSectionEdit(
  kind: 'add' | 'del' | 'upd',
  path: string,
  secLine: number,
  content: { line: number; text: string }[],
  strict: boolean,
): Edit {
  if (kind === 'add') {
    const fileLines: string[] = [];
    for (const c of content) {
      if (c.text === '') fileLines.push('');
      else if (c.text[0] === '+') fileLines.push(c.text.slice(1));
      else throw new Exit2(`error: parse ${c.line}`);
    }
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, serializeCreated(fileLines, true));
    };
  }
  if (kind === 'del') {
    if (content.length > 0) throw new Exit2(`error: parse ${content[0]!.line}`);
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) === null) throw new Fail('missing', path);
      tree.now.set(path, null);
    };
  }
  // Update File.
  let moveTo: string | undefined;
  let idx = 0;
  if (content.length > 0 && content[0]!.text.startsWith('*** Move to: ')) {
    moveTo = content[0]!.text.slice(13).trim();
    idx = 1;
  }
  const chunks: VChunk[] = [];
  while (idx < content.length) {
    const c = content[idx]!;
    if (c.text.startsWith('@@')) {
      const anchorText = c.text.slice(2).trim();
      const chunk: VChunk = { anchor: anchorText === '' ? null : anchorText, eof: false, body: [] };
      idx = readVBody(content, idx + 1, chunk);
      if (idx < content.length && content[idx]!.text.trim() === '*** End of File') {
        chunk.eof = true;
        idx += 1;
      }
      chunks.push(chunk);
    } else if (isVBodyLine(c.text)) {
      if (chunks.length > 0) throw new Exit2(`error: parse ${c.line}`);
      const chunk: VChunk = { anchor: null, eof: false, body: [] };
      idx = readVBody(content, idx, chunk);
      if (idx < content.length && content[idx]!.text.trim() === '*** End of File') {
        chunk.eof = true;
        idx += 1;
      }
      chunks.push(chunk);
    } else {
      throw new Exit2(`error: parse ${c.line}`);
    }
  }
  if (chunks.length === 0 && moveTo === undefined) throw new Exit2(`error: parse ${secLine}`);
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== undefined && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    if (moveTo !== undefined && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const model = parseFile(text);
    let cursor = 0;
    for (const chunk of chunks) {
      const o = chunk.body.filter((b) => b.kind !== 'plus');
      const n = chunk.body.filter((b) => b.kind !== 'minus');
      if (chunk.anchor !== null) {
        const tiers = strict ? [0] : [0, 1, 2];
        let at = -1;
        for (const t of tiers) {
          for (let p = cursor; p < model.lines.length; p += 1) {
            if (tierEq(model.lines[p]!, chunk.anchor, t)) {
              at = p;
              break;
            }
          }
          if (at >= 0) break;
        }
        if (at < 0) throw new Fail('no-match', path);
        cursor = at + 1;
      }
      if (o.length === 0) {
        const pos = chunk.eof ? model.lines.length : Math.min(cursor, model.lines.length);
        model.lines.splice(pos, 0, ...n.map((e) => e.text));
        cursor = pos + n.length;
      } else {
        const found = findTierFrom(model.lines, o.map((e) => e.text), strict, cursor, chunk.eof);
        if (found === null) throw new Fail('no-match', path);
        const pos = found.positions[0]!;
        const repl = buildReplacement(model.lines, pos, o, n, found.tier);
        model.lines.splice(pos, o.length, ...repl);
        cursor = pos + repl.length;
      }
    }
    const result = serialize(model);
    if (moveTo !== undefined) {
      tree.now.set(path, null);
      tree.now.set(moveTo, result);
      tree.moves.push([path, moveTo]);
    } else {
      tree.now.set(path, result);
    }
  };
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const f = lines.findIndex((l) => !blank(l));
  if (f < 0) throw new Exit2('error: parse 1');
  if (lines[f]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${f + 1}`);
  let l = lines.length - 1;
  while (l >= 0 && blank(lines[l]!)) l -= 1;
  if (lines[l]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const secStart = (t: string): 'add' | 'del' | 'upd' | null =>
    t.startsWith('*** Add File: ') ? 'add' : t.startsWith('*** Delete File: ') ? 'del' : t.startsWith('*** Update File: ') ? 'upd' : null;
  const edits: Edit[] = [];
  let i = f + 1;
  while (i < l) {
    const line = lines[i]!;
    if (blank(line)) {
      i += 1;
      continue;
    }
    const kind = secStart(line);
    if (kind === null) throw new Exit2(`error: parse ${i + 1}`);
    const prefix = kind === 'add' ? '*** Add File: ' : kind === 'del' ? '*** Delete File: ' : '*** Update File: ';
    const path = line.slice(prefix.length).trim();
    const content: { line: number; text: string }[] = [];
    let j = i + 1;
    while (j < l && secStart(lines[j]!) === null) {
      content.push({ line: j + 1, text: lines[j]! });
      j += 1;
    }
    while (content.length > 0 && blank(content[content.length - 1]!.text)) content.pop();
    edits.push(v4aSectionEdit(kind, path, i + 1, content, strict));
    i = j;
  }
  return edits;
}

// Sections 1, 2 and 10: the command line, the output and exit codes, and the all-or-nothing write.

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? srEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  interface Row {
    key: string;
    line: string;
  }
  const rows: Row[] = [];
  const byPath = new Map<string, Row>();
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    const row: Row = { key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` };
    rows.push(row);
    byPath.set(p, row);
  }
  for (const [o, nw] of tree.moves) {
    const dRow = byPath.get(o);
    const aRow = byPath.get(nw);
    if (dRow !== undefined && aRow !== undefined && dRow.line.startsWith('D ') && aRow.line.startsWith('A ')) {
      rows.splice(rows.indexOf(dRow), 1);
      rows.splice(rows.indexOf(aRow), 1);
      rows.push({ key: nw, line: `R ${o} -> ${nw}` });
    }
  }
  rows.sort((x, y) => Buffer.compare(Buffer.from(x.key), Buffer.from(y.key)));
  if (!check) {
    for (const [p, now] of tree.now) {
      if (tree.original(p) === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
