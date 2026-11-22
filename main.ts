// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

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

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** Moves performed by edits of this run, for the R output lines (SPEC.md section 2). */
const moves: { from: string; to: string }[] = [];

/** `--strict` allows only tier 0 (SPEC.md section 5); set from run() before edits apply. */
let strictMode = false;

const leadingWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};

/** A file as lines: its line break, and whether it ends with one (SPEC.md section 3). */
interface FileLines {
  lines: string[];
  br: string;
  final: boolean;
}

function splitFile(text: string): FileLines {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const final = text.endsWith(br);
  const parts = text.split(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}

function joinFile(f: FileLines): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

const stripTrail = (s: string): string => s.replace(/[ \t]+$/, '');
const stripBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripTrail(a) === stripTrail(b);
  return stripBoth(a) === stripBoth(b);
}

/** Positions where the non-empty O occurs in fl at one tier. */
function occurrencesAt(fl: string[], O: string[], tier: number): number[] {
  const pos: number[] = [];
  for (let i = 0; i + O.length <= fl.length; i++) {
    let ok = true;
    for (let j = 0; j < O.length; j++) {
      if (!lineEq(fl[i + j]!, O[j]!, tier)) { ok = false; break; }
    }
    if (ok) pos.push(i);
  }
  return pos;
}

/** First tier at which O occurs at least once, with its positions (SPEC.md section 5). */
function findTier(fl: string[], O: string[]): { tier: number; pos: number[] } | null {
  const maxTier = strictMode ? 0 : 2;
  for (let tier = 0; tier <= maxTier; tier++) {
    const pos = occurrencesAt(fl, O, tier);
    if (pos.length > 0) return { tier, pos };
  }
  return null;
}

/**
 * Replace the O lines at `at` with N. Context lines of N are written as the file's own matched
 * lines; at tier 2 every other line of N is re-indented (SPEC.md section 5).
 */
function replaceAt(fl: string[], at: number, O: string[], N: string[], oCtx: boolean[], nCtx: boolean[], tier: number): string[] {
  const out = fl.slice(0, at);
  const oCtxIdx: number[] = [];
  O.forEach((_, i) => { if (oCtx[i]) oCtxIdx.push(i); });
  let seen = 0;
  const F = tier === 2 ? leadingWs(fl[at] ?? '') : '';
  const P = tier === 2 ? leadingWs(O[0] ?? '') : '';
  for (let ni = 0; ni < N.length; ni++) {
    if (nCtx[ni]) {
      out.push(fl[at + oCtxIdx[seen]!]!);
      seen += 1;
    } else {
      let line = N[ni]!;
      if (tier === 2 && line !== '' && !/^[ \t]*$/.test(line) && line.startsWith(P)) line = F + line.slice(P.length);
      out.push(line);
    }
  }
  out.push(...fl.slice(at + O.length));
  return out;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
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

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
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
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
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

interface Hunk {
  a: number;
  oLines: string[];
  nLines: string[];
  oCtx: boolean[];
  nCtx: boolean[];
  /** a `\` line follows the hunk's last context or `+` line */
  noFinal: boolean;
  /** a `\` line follows the hunk's last `+` line */
  noFinalAfterPlus: boolean;
}

interface Section {
  oldPath: string | null;
  newPath: string | null;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const DIFF_GIT_RE = /^diff --git a\/(\S+) b\/(\S+)\s*$/;

function stripAB(p: string): string {
  return p.startsWith('a/') || p.startsWith('b/') ? p.slice(2) : p;
}

/** A `--- `/`+++ ` path: text after the four characters, up to the first tab, trimmed. */
function headerPath(line: string): string | null {
  const t = line.slice(4).split('\t')[0]!.trim();
  if (t === '/dev/null') return null;
  return stripAB(t);
}

interface SectionDraft {
  oldPath: string | null | undefined;
  newPath: string | null | undefined;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
  diffOld: string | undefined;
  diffNew: string | undefined;
  renameOld: string | undefined;
  renameNew: string | undefined;
  hasHeaderPair: boolean;
}

function unifiedEdits(lines: string[]): Edit[] {
  const drafts: SectionDraft[] = [];
  let cur: SectionDraft | null = null;
  const startSection = (): SectionDraft => {
    const s: SectionDraft = { oldPath: undefined, newPath: undefined, newFile: false, deletedFile: false, hunks: [], diffOld: undefined, diffNew: undefined, renameOld: undefined, renameNew: undefined, hasHeaderPair: false };
    drafts.push(s);
    cur = s;
    return s;
  };
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line === 'diff --git' || line.startsWith('diff --git ')) {
      const m = DIFF_GIT_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const s = startSection();
      s.diffOld = m[1]!;
      s.diffNew = m[2]!;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && cur.hunks.length === 0 && !cur.hasHeaderPair) {
        cur.oldPath = headerPath(line);
        cur.newPath = headerPath(lines[i + 1]!);
        cur.hasHeaderPair = true;
      } else {
        const s = startSection();
        s.oldPath = headerPath(line);
        s.newPath = headerPath(lines[i + 1]!);
        s.hasHeaderPair = true;
      }
      i += 2;
      continue;
    }
    if (line.startsWith('--- ')) {
      if (cur !== null && cur.hunks.length === 0) throw new Exit2(`error: parse ${i + 2}`);
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      const m = HUNK_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const a = Number(m[1]);
      const body: string[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const bl = lines[j]!;
        if (bl === 'diff --git' || bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) { body.push(bl); j++; continue; }
        break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      const oLines: string[] = [];
      const nLines: string[] = [];
      const oCtx: boolean[] = [];
      const nCtx: boolean[] = [];
      for (const bl of body) {
        if (bl.startsWith('\\')) continue;
        if (bl.startsWith(' ')) { oLines.push(bl.slice(1)); nLines.push(bl.slice(1)); oCtx.push(true); nCtx.push(true); }
        else if (bl.startsWith('-')) { oLines.push(bl.slice(1)); oCtx.push(false); }
        else if (bl.startsWith('+')) { nLines.push(bl.slice(1)); nCtx.push(false); }
        else { oLines.push(''); nLines.push(''); oCtx.push(true); nCtx.push(true); }
      }
      let lastCtxPlus = -1;
      let lastPlus = -1;
      for (let k = 0; k < body.length; k++) {
        if (body[k]!.startsWith(' ') || body[k]!.startsWith('+') || body[k] === '') lastCtxPlus = k;
        if (body[k]!.startsWith('+')) lastPlus = k;
      }
      const noFinal = lastCtxPlus >= 0 && body[lastCtxPlus + 1] !== undefined && body[lastCtxPlus + 1]!.startsWith('\\');
      const noFinalAfterPlus = lastPlus >= 0 && body[lastPlus + 1] !== undefined && body[lastPlus + 1]!.startsWith('\\');
      cur.hunks.push({ a, oLines, nLines, oCtx, nCtx, noFinal, noFinalAfterPlus });
      i = j;
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (line.startsWith('rename from ')) cur.renameOld = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) cur.renameNew = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) cur.newFile = true;
      else if (line.startsWith('deleted file mode')) cur.deletedFile = true;
    }
    i++;
  }
  const edits: Edit[] = [];
  for (const d of drafts) {
    let oldPath: string | null;
    let newPath: string | null;
    if (d.hasHeaderPair) {
      oldPath = d.oldPath ?? null;
      newPath = d.newPath ?? null;
    } else {
      oldPath = d.renameOld !== undefined ? d.renameOld : d.diffOld !== undefined ? d.diffOld : null;
      newPath = d.renameNew !== undefined ? d.renameNew : d.diffNew !== undefined ? d.diffNew : null;
    }
    edits.push(unifiedSectionEdit({ oldPath, newPath, newFile: d.newFile, deletedFile: d.deletedFile, hunks: d.hunks }));
  }
  return edits;
}

/** Apply a section's hunks in order to a file's text (SPEC.md section 6). */
function applyHunks(text: string, hunks: Hunk[], path: string): string {
  const f = splitFile(text);
  let d = 0;
  for (const h of hunks) {
    if (h.oLines.length === 0) {
      if (h.nLines.length === 0) continue;
      const at = Math.max(0, Math.min(h.a + d, f.lines.length));
      if (at === f.lines.length) f.final = !h.noFinal;
      f.lines.splice(at, 0, ...h.nLines);
      d += h.nLines.length;
      continue;
    }
    const found = findTier(f.lines, h.oLines);
    if (found === null) throw new Fail('no-match', path);
    const target = h.a - 1 + d;
    let best = found.pos[0]!;
    for (const p of found.pos) {
      if (Math.abs(p - target) < Math.abs(best - target)) best = p;
    }
    if (best + h.oLines.length === f.lines.length) f.final = !h.noFinal;
    f.lines = replaceAt(f.lines, best, h.oLines, h.nLines, h.oCtx, h.nCtx, found.tier);
    d += h.nLines.length - h.oLines.length;
  }
  return joinFile(f);
}

/** A created file is the `+` lines of all its hunks, in order (SPEC.md section 6). */
function creationText(hunks: Hunk[]): string {
  const plus: string[] = [];
  let final = true;
  for (const h of hunks) {
    let hasPlus = false;
    for (let k = 0; k < h.nLines.length; k++) {
      if (!h.nCtx[k]) { plus.push(h.nLines[k]!); hasPlus = true; }
    }
    if (hasPlus) final = !h.noFinalAfterPlus;
  }
  if (plus.length === 0) return '';
  return plus.join('\n') + (final ? '\n' : '');
}

function unifiedSectionEdit(sec: Section): Edit {
  return (tree) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    const isCreate = oldP === null || sec.newFile;
    const isDelete = !isCreate && (newP === null || sec.deletedFile);
    if (isCreate) {
      if (newP === null) return;
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      tree.now.set(newP, creationText(sec.hunks));
      return;
    }
    if (isDelete) {
      if (tree.get(oldP!) === null) throw new Fail('missing', oldP!);
      tree.now.set(oldP!, null);
      return;
    }
    if (oldP !== newP) {
      const before = tree.get(oldP!);
      if (before === null) throw new Fail('missing', oldP!);
      if (tree.get(newP!) !== null) throw new Fail('exists', newP!);
      const out = applyHunks(before, sec.hunks, oldP!);
      tree.now.set(oldP!, null);
      tree.now.set(newP!, out);
      moves.push({ from: oldP!, to: newP! });
      return;
    }
    const before = tree.get(oldP!);
    if (before === null) throw new Fail('missing', oldP!);
    tree.now.set(oldP!, applyHunks(before, sec.hunks, oldP!));
  };
}

interface SrBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function searchReplaceEdits(lines: string[]): Edit[] {
  const blocks: SrBlock[] = [];
  let prevReplace = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') { i++; continue; }
    const searchNo = i + 1;
    let path: string | null = null;
    for (let j = i - 1; j > prevReplace; j--) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new Exit2(`error: parse ${searchNo}`);
    let eq = -1;
    for (let k = i + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '=======') { eq = k; break; }
    }
    if (eq === -1) throw new Exit2(`error: parse ${searchNo}`);
    let rep = -1;
    for (let k = eq + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') { rep = k; break; }
    }
    if (rep === -1) throw new Exit2(`error: parse ${searchNo}`);
    blocks.push({ path, oldLines: lines.slice(i + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevPath = path;
    prevReplace = rep;
    i = rep + 1;
  }
  return blocks.map((b) => srEdit(b));
}

function srEdit(b: SrBlock): Edit {
  return (tree) => {
    const p = b.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (b.oldLines.length === 0) {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, b.newLines.length === 0 ? '' : `${b.newLines.join('\n')}\n`);
      return;
    }
    const before = tree.get(p);
    if (before === null) throw new Fail('missing', p);
    const f = splitFile(before);
    const found = findTier(f.lines, b.oldLines);
    if (found === null) throw new Fail('no-match', p);
    if (found.pos.length > 1) throw new Fail('ambiguous', p);
    const at = found.pos[0]!;
    f.lines = replaceAt(f.lines, at, b.oldLines, b.newLines, b.oldLines.map(() => false), b.newLines.map(() => false), found.tier);
    tree.now.set(p, joinFile(f));
  };
}

interface VChunk {
  anchor: string | null;
  endOfFile: boolean;
  oLines: string[];
  nLines: string[];
  oCtx: boolean[];
  nCtx: boolean[];
}

const V4A_SECTION_RE = /^\*\*\* (Add File|Delete File|Update File): /;

function v4aEdits(lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) { last = i; break; }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) { i++; continue; }
    let m: RegExpExecArray | null;
    if ((m = /^\*\*\* Add File: (.*)$/.exec(line)) !== null) {
      const p = m[1]!.trim();
      i++;
      const raw: { text: string; no: number }[] = [];
      while (i < last) {
        const l = lines[i]!;
        if (V4A_SECTION_RE.test(l)) break;
        raw.push({ text: l, no: i + 1 });
        i++;
      }
      while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
      const fileLines: string[] = [];
      for (const r of raw) {
        if (r.text === '') fileLines.push('');
        else if (r.text.startsWith('+')) fileLines.push(r.text.slice(1));
        else throw new Exit2(`error: parse ${r.no}`);
      }
      edits.push(v4aAddEdit(p, fileLines));
      continue;
    }
    if ((m = /^\*\*\* Delete File: (.*)$/.exec(line)) !== null) {
      const p = m[1]!.trim();
      i++;
      const raw: { text: string; no: number }[] = [];
      while (i < last) {
        const l = lines[i]!;
        if (V4A_SECTION_RE.test(l)) break;
        raw.push({ text: l, no: i + 1 });
        i++;
      }
      for (const r of raw) {
        if (!blank(r.text)) throw new Exit2(`error: parse ${r.no}`);
      }
      edits.push(v4aDeleteEdit(p));
      continue;
    }
    if ((m = /^\*\*\* Update File: (.*)$/.exec(line)) !== null) {
      const p = m[1]!.trim();
      const updateNo = i + 1;
      i++;
      const raw: { text: string; no: number }[] = [];
      while (i < last) {
        const l = lines[i]!;
        if (V4A_SECTION_RE.test(l)) break;
        raw.push({ text: l, no: i + 1 });
        i++;
      }
      while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
      edits.push(v4aUpdateEdit(p, updateNo, raw));
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function v4aAddEdit(p: string, fileLines: string[]): Edit {
  return (tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    if (tree.get(p) !== null) throw new Fail('exists', p);
    tree.now.set(p, fileLines.length === 0 ? '' : `${fileLines.join('\n')}\n`);
  };
}

function v4aDeleteEdit(p: string): Edit {
  return (tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    if (tree.get(p) === null) throw new Fail('missing', p);
    tree.now.set(p, null);
  };
}

function v4aUpdateEdit(p: string, updateNo: number, raw: { text: string; no: number }[]): Edit {
  let moveTo: string | null = null;
  let j = 0;
  while (j < raw.length && blank(raw[j]!.text)) j++;
  let chunkLines = raw;
  if (j < raw.length) {
    const mm = /^\*\*\* Move to: (.*)$/.exec(raw[j]!.text);
    if (mm !== null) {
      moveTo = mm[1]!.trim();
      chunkLines = raw.slice(j + 1);
    }
  }
  const chunks: VChunk[] = [];
  let cur: VChunk | null = null;
  let seenChunk = false;
  for (const r of chunkLines) {
    const l = r.text;
    if (l.startsWith('@@')) {
      const anch = l.slice(2).trim();
      cur = { anchor: anch === '' ? null : anch, endOfFile: false, oLines: [], nLines: [], oCtx: [], nCtx: [] };
      chunks.push(cur);
      seenChunk = true;
      continue;
    }
    if (l.trim() === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${r.no}`);
      cur.endOfFile = true;
      cur = null;
      continue;
    }
    if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
      if (cur === null) {
        if (seenChunk) {
          if (l === '') continue;
          throw new Exit2(`error: parse ${r.no}`);
        }
        cur = { anchor: null, endOfFile: false, oLines: [], nLines: [], oCtx: [], nCtx: [] };
        chunks.push(cur);
        seenChunk = true;
      }
      if (l === '') { cur.oLines.push(''); cur.nLines.push(''); cur.oCtx.push(true); cur.nCtx.push(true); }
      else if (l.startsWith(' ')) { cur.oLines.push(l.slice(1)); cur.nLines.push(l.slice(1)); cur.oCtx.push(true); cur.nCtx.push(true); }
      else if (l.startsWith('-')) { cur.oLines.push(l.slice(1)); cur.oCtx.push(false); }
      else { cur.nLines.push(l.slice(1)); cur.nCtx.push(false); }
      continue;
    }
    throw new Exit2(`error: parse ${r.no}`);
  }
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateNo}`);
  return (tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(p);
    if (before === null) throw new Fail('missing', p);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const f = splitFile(before);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null) {
        let idx = -1;
        const maxTier = strictMode ? 0 : 2;
        for (let tier = 0; tier <= maxTier && idx < 0; tier++) {
          for (let k = cursor; k < f.lines.length; k++) {
            if (lineEq(f.lines[k]!, ch.anchor, tier)) { idx = k; break; }
          }
        }
        if (idx < 0) throw new Fail('no-match', p);
        cursor = idx + 1;
      }
      if (ch.oLines.length === 0) {
        const at = ch.endOfFile ? f.lines.length : cursor;
        f.lines.splice(at, 0, ...ch.nLines);
        cursor = at + ch.nLines.length;
        continue;
      }
      let found: { tier: number; pos: number[] } | null = null;
      const maxTier = strictMode ? 0 : 2;
      for (let tier = 0; tier <= maxTier; tier++) {
        const pos = occurrencesAt(f.lines, ch.oLines, tier).filter((q) => q >= cursor && (!ch.endOfFile || q + ch.oLines.length === f.lines.length));
        if (pos.length > 0) { found = { tier, pos }; break; }
      }
      if (found === null) throw new Fail('no-match', p);
      const at = found.pos[0]!;
      f.lines = replaceAt(f.lines, at, ch.oLines, ch.nLines, ch.oCtx, ch.nCtx, found.tier);
      cursor = at + ch.nLines.length;
    }
    const out = joinFile(f);
    if (moveTo !== null) {
      tree.now.set(p, null);
      tree.now.set(moveTo, out);
      moves.push({ from: p, to: moveTo });
    } else {
      tree.now.set(p, out);
    }
  };
}

function run(args: string[]): { code: number; out: string[] } {
  moves.length = 0;
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
  strictMode = strict;
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
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines);
    else edits = v4aEdits(lines);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: { key: string; line: string }[] = [];
  const movePairs = moves.filter((mv) => {
    const wasOld = tree.original(mv.from);
    const nowOld = tree.get(mv.from);
    const wasNew = tree.original(mv.to);
    const nowNew = tree.get(mv.to);
    return wasOld !== null && nowOld === null && wasNew === null && nowNew !== null;
  });
  const movedFrom = new Set(movePairs.map((mv) => mv.from));
  const movedTo = new Set(movePairs.map((mv) => mv.to));
  for (const p of [...tree.now.keys()]) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (movedFrom.has(p) || movedTo.has(p)) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const mv of movePairs) rows.push({ key: mv.to, line: `R ${mv.from} -> ${mv.to}` });
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  const outLines = rows.map((r) => r.line);
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
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
