// github-core-clone-01: a standalone GitHub-compatible git forge in one process.
//
// Serves git smart HTTP (upload-pack v2 + v0, receive-pack v0), REST v3,
// GraphQL v4 and MCP from one in-memory store. Node 22 stdlib only.
//
// The viewer is the login the trial token names. The suite's scenario is built
// from one fixed seed (kit sdk/conformance/wire.ts SCENARIO_SEED), so the viewer
// login is the same in every trial: adaiversen (id 1000). Any other owner in a
// repository path is a stranger: their repositories are 404, never 403.

import { createHash, timingSafeEqual } from 'node:crypto';
import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { deflateSync, inflateSync } from 'node:zlib';

export const VIEWER_LOGIN = 'adaiversen';
export const VIEWER_ID = 1000;
export const VIEWER_NAME = 'ada iversen';
export const VIEWER_EMAIL = 'adaiversen@example.invalid';
export const STRANGER_LOGIN = 'olgabauer';
const ZERO_OID = '0'.repeat(40);
// Fixed epoch for every timestamp the forge itself stamps (commits, issues,
// pull requests): no wall clock ever reaches stored state, so two runs of the
// same operation sequence leave byte-identical state.
const EPOCH_SEC = 1735689600;
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';

// ---------------------------------------------------------------------------
// small helpers

function sha1(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}
function hashObject(type: string, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1(Buffer.concat([header, data]));
}
function isOid(v: string): boolean {
  return /^[0-9a-f]{40}$/.test(v);
}
function b64encode(data: Buffer): string {
  return data.toString('base64');
}
function b64decode(text: string): Buffer {
  return Buffer.from(text.replace(/\s+/g, ''), 'base64');
}
function isoOf(seq: number): string {
  return new Date((EPOCH_SEC + seq) * 1000).toISOString();
}
function escJson(s: string): string {
  return JSON.stringify(s);
}

// ---------------------------------------------------------------------------
// pkt-line framing

function pktLine(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = body.length + 4;
  const head = Buffer.alloc(4);
  head.write(len.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, body]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
const PKT_END = Buffer.from('0002', 'ascii');

interface Pkt {
  kind: 'data' | 'flush' | 'delim' | 'end';
  payload: Buffer;
}

/** Decode a whole buffer of pkt-lines. Throws on garbage. */
function decodePktLines(buf: Buffer): Pkt[] {
  const out: Pkt[] = [];
  let i = 0;
  while (i < buf.length) {
    if (i + 4 > buf.length) throw new Error('truncated pkt-line header');
    const hex = buf.subarray(i, i + 4).toString('ascii');
    if (hex === '0000') { out.push({ kind: 'flush', payload: Buffer.alloc(0) }); i += 4; continue; }
    if (hex === '0001') { out.push({ kind: 'delim', payload: Buffer.alloc(0) }); i += 4; continue; }
    if (hex === '0002') { out.push({ kind: 'end', payload: Buffer.alloc(0) }); i += 4; continue; }
    const len = parseInt(hex, 16);
    if (!Number.isFinite(len) || len < 4 || i + len > buf.length) throw new Error('bad pkt-line length');
    out.push({ kind: 'data', payload: Buffer.from(buf.subarray(i + 4, i + len)) });
    i += len;
  }
  return out;
}

// ---------------------------------------------------------------------------
// git objects

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObject { type: ObjType; data: Buffer; }
interface TreeEntry { mode: string; name: string; oid: string; }

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let i = 0;
  while (i < data.length) {
    const sp = data.indexOf(0x20, i);
    if (sp < 0) throw new Error('bad tree entry');
    const mode = data.subarray(i, sp).toString('ascii');
    const nul = data.indexOf(0, sp);
    if (nul < 0 || nul + 21 > data.length) throw new Error('bad tree entry');
    const name = data.subarray(sp + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    i = nul + 21;
  }
  return entries;
}

function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const an = a.mode === '40000' ? `${a.name}/` : a.name;
    const bn = b.mode === '40000' ? `${b.name}/` : b.name;
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

interface CommitView { tree: string; parents: string[]; author: string; committer: string; message: string; }

function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const headEnd = text.indexOf('\n\n');
  const head = headEnd >= 0 ? text.slice(0, headEnd) : text;
  const message = headEnd >= 0 ? text.slice(headEnd + 2) : '';
  const parents: string[] = [];
  let tree = '';
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, author, committer, message };
}

function parseTag(data: Buffer): { object: string; type: string; tag: string; message: string } {
  const text = data.toString('utf8');
  const headEnd = text.indexOf('\n\n');
  const head = headEnd >= 0 ? text.slice(0, headEnd) : text;
  const message = headEnd >= 0 ? text.slice(headEnd + 2) : '';
  let object = '';
  let type = '';
  let tag = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line.startsWith('tag ')) tag = line.slice(4).trim();
  }
  return { object, type, tag, message };
}

function buildCommitText(tree: string, parents: string[], message: string, ts: number): Buffer {
  const ident = `${VIEWER_NAME} <${VIEWER_EMAIL}> ${ts} +0000`;
  let s = `tree ${tree}\n`;
  for (const p of parents) s += `parent ${p}\n`;
  s += `author ${ident}\ncommitter ${ident}\n\n${message.endsWith('\n') ? message : `${message}\n`}`;
  return Buffer.from(s, 'utf8');
}

// --- packfile write (no deltas) and read (with delta support) ---

function writePackObjectHeader(type: ObjType, size: number): Buffer {
  const typeNum: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
  const bytes: number[] = [];
  let first = (typeNum[type] << 4) | (size & 0x0f);
  size >>= 4;
  if (size > 0) first |= 0x80;
  bytes.push(first);
  while (size > 0) {
    let b = size & 0x7f;
    size >>= 7;
    if (size > 0) b |= 0x80;
    bytes.push(b);
  }
  return Buffer.from(bytes);
}

function writePack(objects: GitObject[]): Buffer {
  const parts: Buffer[] = [Buffer.from('PACK', 'ascii')];
  const ver = Buffer.alloc(4); ver.writeUInt32BE(2, 0); parts.push(ver);
  const count = Buffer.alloc(4); count.writeUInt32BE(objects.length, 0); parts.push(count);
  for (const obj of objects) {
    parts.push(writePackObjectHeader(obj.type, obj.data.length));
    parts.push(deflateSync(obj.data, { level: 6 }));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

function readVarintSize(buf: Buffer, start: number): { size: number; next: number; first: number } {
  let size = buf[start]! & 0x0f;
  const first = (buf[start]! >> 4) & 0x07;
  let shift = 4;
  let i = start + 1;
  while (buf[i - 1]! & 0x80) {
    size |= (buf[i]! & 0x7f) << shift;
    shift += 7;
    i += 1;
  }
  return { size, next: i, first };
}

function inflateAt(buf: Buffer, offset: number): { data: Buffer; next: number } {
  // One pass over the deflate bitstream finds the zlib stream's exact end
  // (deflateEndOffset), then a single inflateSync decodes it. The old code
  // binary-searched the end with ~log2(n) inflateSync calls per object.
  const end = deflateEndOffset(buf, offset);
  const data = inflateSync(buf.subarray(offset, end));
  return { data, next: end };
}

// --- skip-only DEFLATE scanner: finds a zlib stream's end without decoding ---
// DEFLATE (RFC 1951) bit order is LSB-first within bytes; Huffman codes are
// read MSB-first. This scanner walks the block structure and skips every
// literal/length/distance symbol without emitting output, so it costs one
// linear pass instead of ~log2(n) full inflates.

const CLEN_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

class DeflateBitReader {
  buf: Buffer; pos: number; bit = 0;
  constructor(buf: Buffer, start: number) { this.buf = buf; this.pos = start; }
  read(n: number): number {
    let v = 0;
    for (let i = 0; i < n; i += 1) {
      if (this.pos >= this.buf.length) throw new Error('deflate: overrun');
      v |= ((this.buf[this.pos]! >> this.bit) & 1) << i;
      this.bit += 1;
      if (this.bit === 8) { this.bit = 0; this.pos += 1; }
    }
    return v;
  }
  alignByte(): void { if (this.bit !== 0) { this.bit = 0; this.pos += 1; } }
  bytePos(): number { return this.bit === 0 ? this.pos : this.pos + 1; }
}

interface HuffmanDecoder { decode(br: DeflateBitReader): number; }

function buildHuffmanDecoder(lengths: number[]): HuffmanDecoder {
  // Canonical Huffman decoder, array-only (no per-bit Map/string keys: the
  // scanner runs on every pack object, so decode must stay allocation-free).
  const maxLen = Math.max(0, ...lengths);
  const count = new Array<number>(maxLen + 1).fill(0);
  for (const l of lengths) if (l > 0) count[l]! += 1;
  const firstCode = new Array<number>(maxLen + 1).fill(0);
  const firstIndex = new Array<number>(maxLen + 1).fill(0);
  let code = 0;
  let idx = 0;
  for (let len = 1; len <= maxLen; len += 1) {
    code = (code + (count[len - 1] ?? 0)) << 1;
    firstCode[len] = code;
    firstIndex[len] = idx;
    idx += count[len]!;
  }
  const symbols = new Array<number>(idx);
  const nextCode = [...firstCode];
  for (let sym = 0; sym < lengths.length; sym += 1) {
    const len = lengths[sym]!;
    if (len === 0) continue;
    symbols[firstIndex[len]! + (nextCode[len]! - firstCode[len]!)] = sym;
    nextCode[len]! += 1;
  }
  return {
    decode(br: DeflateBitReader): number {
      const buf = br.buf;
      let c = 0;
      for (let len = 1; len <= maxLen; len += 1) {
        // Inlined single-bit read: the scanner's hot loop.
        if (br.pos >= buf.length) throw new Error('deflate: overrun');
        c = (c << 1) | ((buf[br.pos]! >> br.bit) & 1);
        br.bit += 1;
        if (br.bit === 8) { br.bit = 0; br.pos += 1; }
        const rel = c - firstCode[len]!;
        if (rel >= 0 && rel < (count[len] ?? 0)) return symbols[firstIndex[len]! + rel]!;
      }
      throw new Error('deflate: bad huffman code');
    },
  };
}

const FIXED_LIT_DECODER: HuffmanDecoder = (() => {
  const lengths = new Array<number>(288).fill(0);
  for (let i = 0; i < 144; i += 1) lengths[i] = 8;
  for (let i = 144; i < 256; i += 1) lengths[i] = 9;
  for (let i = 256; i < 280; i += 1) lengths[i] = 7;
  for (let i = 280; i < 288; i += 1) lengths[i] = 8;
  return buildHuffmanDecoder(lengths);
})();
const FIXED_DIST_DECODER: HuffmanDecoder = buildHuffmanDecoder(new Array<number>(32).fill(5));

const DEFLATE_LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const DEFLATE_LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DEFLATE_DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DEFLATE_DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

function skipDeflateBlock(br: DeflateBitReader, litDec: HuffmanDecoder, distDec: HuffmanDecoder): void {
  for (;;) {
    const sym = litDec.decode(br);
    if (sym === 256) return; // end of block
    if (sym < 256) continue; // literal: skip
    const li = sym - 257;
    if (li < 0 || li >= DEFLATE_LEN_BASE.length) throw new Error('deflate: bad length symbol');
    br.read(DEFLATE_LEN_EXTRA[li]!);
    const dsym = distDec.decode(br);
    if (dsym >= DEFLATE_DIST_BASE.length) throw new Error('deflate: bad distance symbol');
    br.read(DEFLATE_DIST_EXTRA[dsym]!);
  }
}

/** End offset (exclusive) of the zlib stream starting at `start` (which points
 *  at the 2-byte zlib header). Includes the 4-byte adler32. Throws on garbage. */
function deflateEndOffset(buf: Buffer, start: number): number {
  if (start + 2 > buf.length) throw new Error('deflate: truncated header');
  const br = new DeflateBitReader(buf, start + 2);
  for (;;) {
    const bfinal = br.read(1);
    const btype = br.read(2);
    if (btype === 0) {
      br.alignByte();
      if (br.pos + 4 > buf.length) throw new Error('deflate: truncated stored block');
      const len = buf[br.pos]! | (buf[br.pos + 1]! << 8);
      br.pos += 4 + len;
      if (br.pos > buf.length) throw new Error('deflate: stored block overrun');
    } else if (btype === 1) {
      skipDeflateBlock(br, FIXED_LIT_DECODER, FIXED_DIST_DECODER);
    } else if (btype === 2) {
      const hlit = br.read(5) + 257;
      const hdist = br.read(5) + 1;
      const hclen = br.read(4) + 4;
      const clen = new Array<number>(19).fill(0);
      for (let i = 0; i < hclen; i += 1) clen[CLEN_ORDER[i]!] = br.read(3);
      const clDec = buildHuffmanDecoder(clen);
      const lengths = new Array<number>(hlit + hdist).fill(0);
      let i = 0;
      while (i < hlit + hdist) {
        const sym = clDec.decode(br);
        if (sym < 16) { lengths[i] = sym; i += 1; }
        else if (sym === 16) {
          if (i === 0) throw new Error('deflate: repeat with no previous length');
          const rep = 3 + br.read(2);
          const prev = lengths[i - 1]!;
          for (let k = 0; k < rep; k += 1) lengths[i++] = prev;
        } else if (sym === 17) {
          const rep = 3 + br.read(3);
          for (let k = 0; k < rep; k += 1) lengths[i++] = 0;
        } else if (sym === 18) {
          const rep = 11 + br.read(7);
          for (let k = 0; k < rep; k += 1) lengths[i++] = 0;
        } else throw new Error('deflate: bad code-length symbol');
      }
      skipDeflateBlock(br, buildHuffmanDecoder(lengths.slice(0, hlit)), buildHuffmanDecoder(lengths.slice(hlit)));
    } else {
      throw new Error('deflate: bad block type');
    }
    if (bfinal === 1) {
      const end = br.bytePos() + 4; // adler32
      if (end > buf.length) throw new Error('deflate: truncated adler32');
      return end;
    }
  }
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let i = 0;
  const readVarint = (): number => {
    let v = 0; let shift = 0;
    for (;;) {
      const b = delta[i]!; i += 1;
      v |= (b & 0x7f) << shift; shift += 7;
      if (!(b & 0x80)) break;
    }
    return v;
  };
  const srcSize = readVarint();
  const tgtSize = readVarint();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out: Buffer[] = [];
  let total = 0;
  while (i < delta.length) {
    const op = delta[i]!; i += 1;
    if (op & 0x80) {
      let off = 0; let size = 0;
      for (let b = 0; b < 4; b += 1) if (op & (1 << b)) { off |= delta[i]! << (8 * b); i += 1; }
      for (let b = 0; b < 3; b += 1) if (op & (0x10 << b)) { size |= delta[i]! << (8 * b); i += 1; }
      if (size === 0) size = 0x10000;
      out.push(base.subarray(off, off + size));
      total += size;
    } else if (op !== 0) {
      out.push(delta.subarray(i, i + op));
      total += op;
      i += op;
    } else throw new Error('delta op 0');
  }
  if (total !== tgtSize) throw new Error('delta target size mismatch');
  return Buffer.concat(out);
}

interface PackEntry { type: ObjType; data: Buffer; oid: string; }

/** Parse a packfile; resolve deltas against entries in the pack and `baseLookup`. */
function readPack(pack: Buffer, baseLookup?: (oid: string) => GitObject | undefined): Map<string, GitObject> {
  if (pack.length < 12 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('not a packfile');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`pack version ${version}`);
  const count = pack.readUInt32BE(8);
  const entries: PackEntry[] = [];
  const byOffset = new Map<number, PackEntry>();
  let offset = 12;
  const raw: Array<{ type: number; data: Buffer; offset: number; baseOid?: string; baseOffset?: number }> = [];
  for (let n = 0; n < count; n += 1) {
    const start = offset;
    const { size, next, first } = readVarintSize(pack, offset);
    offset = next;
    if (first === 6 || first === 7) {
      let baseOffset: number | undefined;
      let baseOid: string | undefined;
      if (first === 6) {
        let b = pack[offset]!; offset += 1;
        let base = b & 0x7f;
        while (b & 0x80) { b = pack[offset]!; offset += 1; base = ((base + 1) << 7) | (b & 0x7f); }
        baseOffset = start - base;
      } else {
        baseOid = pack.subarray(offset, offset + 20).toString('hex');
        offset += 20;
      }
      const { data, next: after } = inflateAt(pack, offset);
      offset = after;
      raw.push({ type: first, data, offset: start, baseOid, baseOffset });
      void size;
    } else {
      const typeName: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
      const type = typeName[first];
      if (!type) throw new Error(`unknown pack object type ${first}`);
      const { data, next: after } = inflateAt(pack, offset);
      offset = after;
      if (data.length !== size) throw new Error('pack object size mismatch');
      const oid = hashObject(type, data);
      const entry: PackEntry = { type, data, oid };
      entries.push(entry);
      byOffset.set(start, entry);
    }
  }
  const resolve = (r: (typeof raw)[number]): PackEntry => {
    let base: GitObject | undefined;
    if (r.baseOffset !== undefined) {
      const b = byOffset.get(r.baseOffset);
      if (!b) throw new Error('ofs-delta base missing');
      base = b;
    } else if (r.baseOid !== undefined) {
      base = entries.find((e) => e.oid === r.baseOid) ?? baseLookup?.(r.baseOid);
      if (!base) throw new Error('ref-delta base missing');
    }
    if (!base) throw new Error('delta without base');
    // base itself may be a delta entry already resolved into entries
    const data = applyDelta(base.data, r.data);
    const oid = hashObject(base.type, data);
    const entry: PackEntry = { type: base.type, data, oid };
    entries.push(entry);
    byOffset.set(r.offset, entry);
    return entry;
  };
  // Resolve deltas after all plain entries exist (offsets may point forward in theory).
  for (const r of raw) resolve(r);
  const map = new Map<string, GitObject>();
  for (const e of entries) map.set(e.oid, { type: e.type, data: e.data });
  return map;
}

// ---------------------------------------------------------------------------
// store

interface Label { name: string; color: string; }
interface Issue {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  labels: Label[]; user: string; createdSeq: number; comments: Comment[];
  // Serialized REST JSON for this issue, cached after first build and cleared
  // on any mutation (the read workload GETs one issue 2,000 times).
  jsonCache: Buffer | null;
}
interface Comment { id: number; body: string; user: string; createdSeq: number; }
interface Pull {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  head: string; base: string; headSha: string; baseSha: string;
  merged: boolean; mergedAt: string | null; mergeCommitSha: string | null; createdSeq: number;
}
interface Repo {
  id: number; name: string; owner: string; description: string; priv: boolean;
  defaultBranch: string; createdSeq: number;
  objects: Map<string, GitObject>;
  refs: Map<string, string>;
  labels: Map<string, Label>;
  issues: Issue[]; pulls: Pull[];
  nextIssue: number; nextPull: number; nextComment: number;
  // Perf caches (derived bytes only, never stored state): upload-pack fetch
  // responses and advertisement bodies, keyed on the exact request + a refs
  // fingerprint + object count so a stale hit is impossible.
  packCache: Map<string, Buffer>;
  advCache: Map<string, Buffer>;
}

const repos = new Map<string, Repo>(); // key owner + '/' + name
let nextRepoId = 5000;
let nextGlobalId = 10000;
let seq = 0; // deterministic sequence counter for timestamps

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}
function getRepo(owner: string, name: string): Repo | undefined {
  return repos.get(repoKey(owner, name));
}
function viewerRepos(): Repo[] {
  const out: Repo[] = [];
  for (const r of repos.values()) if (r.owner === VIEWER_LOGIN) out.push(r);
  return out;
}

function createRepoRecord(name: string, description: string, priv: boolean): Repo {
  const repo: Repo = {
    id: nextRepoId++, name, owner: VIEWER_LOGIN, description, priv,
    defaultBranch: 'main', createdSeq: ++seq,
    objects: new Map(), refs: new Map(), labels: new Map(),
    issues: [], pulls: [], nextIssue: 1, nextPull: 1, nextComment: 1,
    packCache: new Map(), advCache: new Map(),
  };
  repos.set(repoKey(VIEWER_LOGIN, name), repo);
  return repo;
}

// --- git graph helpers on a repo ---

function repoObjects(repo: Repo): Map<string, GitObject> {
  return repo.objects;
}

function commitParents(repo: Repo, oid: string): string[] {
  const obj = repo.objects.get(oid);
  if (!obj || obj.type !== 'commit') return [];
  return parseCommit(obj.data).parents;
}

/** All commits reachable from `tips`, in BFS order (newest generations first). */
function reachableCommits(repo: Repo, tips: string[]): string[] {
  const seen = new Set<string>();
  const out: string[] = [];
  const queue = [...tips];
  let head = 0; // index pointer: Array.shift() is O(n) per pop
  while (head < queue.length) {
    const oid = queue[head++]!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    out.push(oid);
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return out;
}

function isAncestor(repo: Repo, anc: string, tip: string): boolean {
  if (anc === tip) return true;
  // Fast path: a push's new commit almost always has the current tip as a
  // direct parent (sequential pushes), so check one hop before any BFS.
  const tipObj = repo.objects.get(tip);
  if (tipObj && tipObj.type === 'commit' && parseCommit(tipObj.data).parents.includes(anc)) return true;
  const seen = new Set<string>([tip]);
  const queue = [tip];
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head++]!;
    for (const p of commitParents(repo, oid)) {
      if (p === anc) return true;
      if (!seen.has(p)) { seen.add(p); queue.push(p); }
    }
  }
  return false;
}

/** Find a merge-base: first common ancestor by BFS from both tips. */
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const fromA = new Set(reachableCommits(repo, [a]));
  const queue = [b];
  const seen = new Set<string>();
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head++]!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (fromA.has(oid)) return oid;
    for (const p of commitParents(repo, oid)) queue.push(p);
  }
  return null;
}

/** Flatten a tree into path -> {oid, mode}. */
function flattenTree(repo: Repo, treeOid: string, prefix = ''): Map<string, { oid: string; mode: string }> {
  const out = new Map<string, { oid: string; mode: string }>();
  const walk = (oid: string, pre: string): void => {
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'tree') return;
    for (const e of parseTree(obj.data)) {
      const path = pre === '' ? e.name : `${pre}/${e.name}`;
      if (e.mode === '40000') walk(e.oid, path);
      else out.set(path, { oid: e.oid, mode: e.mode });
    }
  };
  walk(treeOid, prefix);
  return out;
}

/** Build a tree object from a flat path map, storing intermediate trees. Returns root tree oid. */
function buildTreeFromMap(repo: Repo, files: Map<string, { oid: string; mode: string }>): string {
  interface Node { files: Map<string, { oid: string; mode: string }>; dirs: Map<string, Node>; }
  const make = (): Node => ({ files: new Map(), dirs: new Map() });
  const root = make();
  for (const [path, v] of [...files.entries()].sort()) {
    const segs = path.split('/');
    let node = root;
    for (let i = 0; i < segs.length - 1; i += 1) {
      const s = segs[i]!;
      if (!node.dirs.has(s)) node.dirs.set(s, make());
      node = node.dirs.get(s)!;
    }
    node.files.set(segs[segs.length - 1]!, v);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, v] of node.files) entries.push({ mode: v.mode, name, oid: v.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    const data = buildTree(entries);
    const oid = hashObject('tree', data);
    if (!repo.objects.has(oid)) repo.objects.set(oid, { type: 'tree', data });
    return oid;
  };
  return build(root);
}

function putObject(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

function refTip(repo: Repo, branch: string): string | undefined {
  return repo.refs.get(`refs/heads/${branch}`);
}

function globalId(kind: string, ...parts: (string | number)[]): string {
  return b64encode(Buffer.from(`${kind}:${parts.join(':')}`, 'utf8'));
}
function parseGlobalId(id: string): { kind: string; parts: string[] } | null {
  try {
    const text = b64decode(id).toString('utf8');
    const idx = text.indexOf(':');
    if (idx < 0) return null;
    return { kind: text.slice(0, idx), parts: text.slice(idx + 1).split(':') };
  } catch { return null; }
}

// ---------------------------------------------------------------------------
// HTTP plumbing

const JSON_TYPE = 'application/json; charset=utf-8';
let reqCounter = 0;

function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  const text = status === 204 ? '' : `${JSON.stringify(body)}\n`;
  const headers: Record<string, string> = {
    'x-github-request-id': `req-${++reqCounter}`,
    ...extra,
  };
  if (status !== 204) {
    headers['content-type'] = JSON_TYPE;
    headers['content-length'] = String(Buffer.byteLength(text));
  }
  res.writeHead(status, headers);
  res.end(text);
}

function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, {
    'content-type': contentType,
    'content-length': String(body.length),
    'x-github-request-id': `req-${++reqCounter}`,
  });
  res.end(body);
}

function errJson(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}

interface Ctx {
  req: IncomingMessage;
  res: ServerResponse;
  method: string;
  path: string;
  query: URLSearchParams;
  host: string;
}

function authed(ctx: Ctx): boolean {
  if (TOKEN === '') return true;
  const h = ctx.req.headers.authorization ?? '';
  if (!h.startsWith('Bearer ')) return false;
  const tok = h.slice(7);
  if (tok.length !== TOKEN.length) return false;
  try {
    return timingSafeEqual(Buffer.from(tok), Buffer.from(TOKEN));
  } catch { return false; }
}

function needAuth(ctx: Ctx): boolean {
  if (authed(ctx)) return true;
  errJson(ctx.res, 401, 'Requires authentication');
  return false;
}

async function readBody(req: IncomingMessage, limit = 64 * 1024 * 1024): Promise<Buffer> {
  // Event listeners instead of `for await`: the async-iterator protocol
  // costs a surprising amount per request on tiny bodies (the hot paths
  // read 1 KiB packs and ~100 B JSON bodies).
  return new Promise<Buffer>((resolve, reject) => {
    const chunks: Buffer[] = [];
    let size = 0;
    let done = false;
    req.on('data', (chunk: Buffer) => {
      size += chunk.length;
      if (size > limit) {
        if (!done) { done = true; reject(new Error('body too large')); }
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => { if (!done) { done = true; resolve(Buffer.concat(chunks)); } });
    req.on('error', (err) => { if (!done) { done = true; reject(err); } });
  });
}

async function readJsonBody(ctx: Ctx): Promise<{ ok: true; value: unknown } | { ok: false }> {
  try {
    const raw = await readBody(ctx.req);
    if (raw.length === 0) return { ok: true, value: {} };
    return { ok: true, value: JSON.parse(raw.toString('utf8')) };
  } catch {
    return { ok: false };
  }
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return v !== null && typeof v === 'object' && !Array.isArray(v);
}

// ---------------------------------------------------------------------------
// REST v3 shapes

function repoJson(repo: Repo): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: globalId('Repository', repo.id),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER_ID, node_id: globalId('User', VIEWER_ID), type: 'User', site_admin: false },
    private: repo.priv,
    html_url: `https://github.com/${repo.owner}/${repo.name}`,
    description: repo.description,
    fork: false,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    created_at: isoOf(repo.createdSeq),
    updated_at: isoOf(repo.createdSeq),
    pushed_at: isoOf(repo.createdSeq),
    git_url: `git://github.com/${repo.owner}/${repo.name}.git`,
    ssh_url: `git@github.com:${repo.owner}/${repo.name}.git`,
    clone_url: `https://github.com/${repo.owner}/${repo.name}.git`,
    homepage: null,
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    language: null,
    has_issues: true,
    has_projects: true,
    has_downloads: true,
    has_wiki: true,
    has_pages: false,
    has_discussions: false,
    forks_count: 0,
    archived: false,
    disabled: false,
    open_issues_count: repo.issues.filter((i) => i.state === 'open').length,
    license: null,
    allow_forking: true,
    is_template: false,
    topics: [],
    visibility: repo.priv ? 'private' : 'public',
    default_branch: repo.defaultBranch,
  };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: issue.id,
    node_id: globalId('Issue', repo.id, issue.number),
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    labels_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/labels{/name}`,
    comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/comments`,
    events_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/events`,
    html_url: `https://github.com/${repo.owner}/${repo.name}/issues/${issue.number}`,
    number: issue.number,
    state: issue.state,
    title: issue.title,
    body: issue.body,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, node_id: globalId('User', VIEWER_ID), type: 'User' },
    labels: issue.labels.map((l) => ({ id: nextGlobalId++, node_id: globalId('Label', repo.id, l.name), name: l.name, color: l.color, default: false, description: '' })),
    assignee: null,
    assignees: [],
    milestone: null,
    locked: false,
    comments: issue.comments.length,
    created_at: isoOf(issue.createdSeq),
    updated_at: isoOf(issue.createdSeq),
    closed_at: issue.state === 'closed' ? isoOf(issue.createdSeq) : null,
    author_association: 'OWNER',
    state_reason: issue.state === 'closed' ? 'completed' : null,
  };
}

/** Serialized REST JSON for one issue, cached on the issue after first build. */
function issueJsonBuf(repo: Repo, issue: Issue): Buffer {
  if (issue.jsonCache) return issue.jsonCache;
  const buf = Buffer.from(`${JSON.stringify(issueJson(repo, issue))}\n`, 'utf8');
  issue.jsonCache = buf;
  return buf;
}

/** Drop an issue's cached JSON after any mutation (state, title, body, comments). */
function invalidateIssue(issue: Issue): void {
  issue.jsonCache = null;
}

function sendIssue(ctx: Ctx, status: number, repo: Repo, issue: Issue): void {
  const body = issueJsonBuf(repo, issue);
  ctx.res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': String(body.length),
    'x-github-request-id': `req-${++reqCounter}`,
  });
  ctx.res.end(body);
}

function pullJson(repo: Repo, pr: Pull): Record<string, unknown> {
  return {
    id: pr.id,
    node_id: globalId('PullRequest', repo.id, pr.number),
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pr.number}`,
    html_url: `https://github.com/${repo.owner}/${repo.name}/pull/${pr.number}`,
    number: pr.number,
    state: pr.state,
    locked: false,
    title: pr.title,
    body: pr.body,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, node_id: globalId('User', VIEWER_ID), type: 'User' },
    created_at: isoOf(pr.createdSeq),
    updated_at: isoOf(pr.createdSeq),
    closed_at: pr.state === 'closed' ? isoOf(pr.createdSeq) : null,
    merged_at: pr.mergedAt,
    merge_commit_sha: pr.mergeCommitSha,
    merged: pr.merged,
    mergeable: pr.state === 'open' ? computeMergeable(repo, pr) : null,
    mergeable_state: pr.state === 'open' ? (computeMergeable(repo, pr) ? 'clean' : 'dirty') : 'unknown',
    merged_by: pr.merged ? { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' } : null,
    head: { label: `${VIEWER_LOGIN}:${pr.head}`, ref: pr.head, sha: pr.headSha, user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' }, repo: repoJson(repo) },
    base: { label: `${VIEWER_LOGIN}:${pr.base}`, ref: pr.base, sha: pr.baseSha, user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' }, repo: repoJson(repo) },
    assignee: null,
    assignees: [],
    requested_reviewers: [],
    labels: [],
    milestone: null,
    draft: false,
    commits_url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pr.number}/commits`,
    review_comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pr.number}/comments`,
    comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${pr.number}/comments`,
    statuses_url: `/api/v3/repos/${repo.owner}/${repo.name}/commits/${pr.headSha}/statuses`,
  };
}

function computeMergeable(repo: Repo, pr: Pull): boolean {
  return !prHasConflict(repo, pr);
}

/** True when head and base both changed the same path differently since the merge-base. */
function prHasConflict(repo: Repo, pr: Pull): boolean {
  const baseTip = refTip(repo, pr.base);
  if (!baseTip) return false;
  const mb = mergeBase(repo, pr.headSha, baseTip);
  if (mb === null) return false;
  const mbTree = parseCommit(repo.objects.get(mb)!.data).tree;
  const baseTree = parseCommit(repo.objects.get(baseTip)!.data).tree;
  const headTree = parseCommit(repo.objects.get(pr.headSha)!.data).tree;
  const mbFiles = flattenTree(repo, mbTree);
  const baseFiles = flattenTree(repo, baseTree);
  const headFiles = flattenTree(repo, headTree);
  const paths = new Set([...baseFiles.keys(), ...headFiles.keys()]);
  for (const p of paths) {
    const mbOid = mbFiles.get(p)?.oid ?? null;
    const baseOid = baseFiles.get(p)?.oid ?? null;
    const headOid = headFiles.get(p)?.oid ?? null;
    const baseChanged = baseOid !== mbOid;
    const headChanged = headOid !== mbOid;
    if (baseChanged && headChanged && baseOid !== headOid) return true;
  }
  return false;
}

/** Diff files between two trees: filename, status, additions, deletions, changes. */
function diffFiles(repo: Repo, baseTreeOid: string, headTreeOid: string): Array<Record<string, unknown>> {
  const baseFiles = flattenTree(repo, baseTreeOid);
  const headFiles = flattenTree(repo, headTreeOid);
  const out: Array<Record<string, unknown>> = [];
  const paths = new Set([...baseFiles.keys(), ...headFiles.keys()]);
  for (const p of [...paths].sort()) {
    const b = baseFiles.get(p);
    const h = headFiles.get(p);
    if (b && h && b.oid === h.oid) continue;
    let status = 'modified';
    let additions = 0;
    let deletions = 0;
    const linesOf = (oid: string): string[] => {
      const obj = repo.objects.get(oid);
      if (!obj) return [];
      const t = obj.data.toString('utf8');
      return t === '' ? [] : t.split('\n');
    };
    if (!b && h) {
      status = 'added';
      additions = linesOf(h.oid).length;
    } else if (b && !h) {
      status = 'removed';
      deletions = linesOf(b.oid).length;
    } else if (b && h) {
      const bl = linesOf(b.oid);
      const hl = linesOf(h.oid);
      const bset = new Set(bl);
      const hset = new Set(hl);
      additions = hl.filter((l) => !bset.has(l)).length;
      deletions = bl.filter((l) => !hset.has(l)).length;
      if (additions === 0 && deletions === 0) { additions = 1; }
    }
    out.push({
      sha: h?.oid ?? b?.oid ?? '',
      filename: p,
      status,
      additions,
      deletions,
      changes: additions + deletions,
      blob_url: `https://github.com/blob/${h?.oid ?? ''}`,
      raw_url: `https://github.com/raw/${h?.oid ?? ''}`,
      contents_url: `/api/v3/repos/contents/${encodeURIComponent(p)}`,
      patch: '',
    });
  }
  return out;
}

function commitJson(repo: Repo, oid: string): Record<string, unknown> {
  const obj = repo.objects.get(oid);
  const view = obj ? parseCommit(obj.data) : { tree: '', parents: [], author: '', committer: '', message: '' };
  const parseIdent = (s: string): { name: string; email: string; date: string } => {
    const m = /^(.+?) <([^>]+)> (\d+) ([+-]\d{4})$/.exec(s);
    if (!m) return { name: VIEWER_NAME, email: VIEWER_EMAIL, date: isoOf(0) };
    return { name: m[1]!, email: m[2]!, date: new Date(Number(m[3]) * 1000).toISOString() };
  };
  const author = parseIdent(view.author);
  const committer = parseIdent(view.committer);
  return {
    sha: oid,
    node_id: globalId('Commit', repo.id, oid),
    commit: {
      author,
      committer,
      message: view.message.replace(/\n$/, ''),
      tree: { sha: view.tree, url: `/api/v3/repos/git/trees/${view.tree}` },
      url: `/api/v3/repos/git/commits/${oid}`,
      comment_count: 0,
      verification: { verified: false, reason: 'unsigned', signature: null, payload: null, verified_at: null },
    },
    url: `/api/v3/repos/commits/${oid}`,
    html_url: `https://github.com/commit/${oid}`,
    comments_url: `/api/v3/repos/commits/${oid}/comments`,
    author: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    committer: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    parents: view.parents.map((p) => ({ sha: p, url: `/api/v3/repos/commits/${p}`, html_url: `https://github.com/commit/${p}` })),
  };
}

/** Create a commit on `branch` that sets `path` to `content` (or deletes it). */
function commitFile(
  repo: Repo, branch: string, path: string, content: Buffer | null, message: string,
): { commitSha: string; blobSha: string | null } {
  const tip = refTip(repo, branch);
  let treeOid: string;
  let parent: string[] = [];
  if (tip === undefined) {
    treeOid = buildTreeFromMap(repo, new Map());
  } else {
    const tree = parseCommit(repo.objects.get(tip)!.data).tree;
    parent = [tip];
    treeOid = tree;
  }
  const files = flattenTree(repo, treeOid);
  let blobSha: string | null = null;
  if (content === null) {
    files.delete(path);
  } else {
    blobSha = putObject(repo, 'blob', content);
    files.set(path, { oid: blobSha, mode: '100644' });
  }
  const newTree = buildTreeFromMap(repo, files);
  const ts = EPOCH_SEC + ++seq;
  const data = buildCommitText(newTree, parent, message, ts);
  const commitSha = putObject(repo, 'commit', data);
  repo.refs.set(`refs/heads/${branch}`, commitSha);
  return { commitSha, blobSha };
}

function squashMerge(repo: Repo, pr: Pull): { ok: boolean; sha?: string; conflict?: boolean } {
  const baseTip = refTip(repo, pr.base);
  if (!baseTip) return { ok: false };
  if (prHasConflict(repo, pr)) return { ok: false, conflict: true };
  const mb = mergeBase(repo, pr.headSha, baseTip);
  const baseTree = parseCommit(repo.objects.get(baseTip)!.data).tree;
  const headTree = parseCommit(repo.objects.get(pr.headSha)!.data).tree;
  let files = flattenTree(repo, baseTree);
  if (mb !== null) {
    const mbTree = parseCommit(repo.objects.get(mb)!.data).tree;
    const mbFiles = flattenTree(repo, mbTree);
    const headFiles = flattenTree(repo, headTree);
    files = new Map(files);
    const paths = new Set([...mbFiles.keys(), ...headFiles.keys()]);
    for (const p of paths) {
      const mbOid = mbFiles.get(p)?.oid ?? null;
      const headOid = headFiles.get(p)?.oid ?? null;
      if (headOid !== mbOid) {
        if (headOid === null) files.delete(p);
        else files.set(p, { oid: headOid, mode: headFiles.get(p)!.mode });
      }
    }
  } else {
    files = flattenTree(repo, headTree);
  }
  const newTree = buildTreeFromMap(repo, files);
  const ts = EPOCH_SEC + ++seq;
  const data = buildCommitText(newTree, [baseTip], `Merge pull request #${pr.number} from ${pr.head}\n\n${pr.title}\n`, ts);
  const sha = putObject(repo, 'commit', data);
  repo.refs.set(`refs/heads/${pr.base}`, sha);
  pr.state = 'closed';
  pr.merged = true;
  pr.mergedAt = isoOf(seq);
  pr.mergeCommitSha = sha;
  pr.baseSha = sha;
  return { ok: true, sha };
}

function pageParams(ctx: Ctx): { page: number; perPage: number } {
  const perPage = Math.max(1, Math.min(100, Number(ctx.query.get('per_page') ?? '30') || 30));
  const page = Math.max(1, Number(ctx.query.get('page') ?? '1') || 1);
  return { page, perPage };
}

function paginate<T>(ctx: Ctx, items: T[]): { page: T[]; link: string | null } {
  const { page, perPage } = pageParams(ctx);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  let link: string | null = null;
  if (start + perPage < items.length) {
    const url = new URL(ctx.req.url ?? '/', `http://${ctx.host}`);
    url.searchParams.set('page', String(page + 1));
    url.searchParams.set('per_page', String(perPage));
    link = `<${url.toString()}>; rel="next"`;
  }
  return { page: slice, link };
}

function sendPage<T>(ctx: Ctx, items: T[]): void {
  const { page, link } = paginate(ctx, items);
  sendJson(ctx.res, 200, page, link ? { link } : {});
}

// ---------------------------------------------------------------------------
// REST router

async function handleRest(ctx: Ctx): Promise<boolean> {
  const p = ctx.path;
  if (!p.startsWith('/api/v3')) return false;
  const rest = p.slice('/api/v3'.length) || '/';
  const m = ctx.method;

  // Public root + meta.
  if (m === 'GET' && (rest === '/' || rest === '')) {
    sendJson(ctx.res, 200, {
      current_user_url: '/api/v3/user',
      current_user_authorizations_html_url: 'https://github.com/settings/applications',
      authorizations_url: '/api/v3/authorizations',
      code_search_url: '/api/v3/search/code?q={query}{&page,per_page,sort,order}',
      commit_search_url: '/api/v3/search/commits?q={query}{&page,per_page,sort,order}',
      emails_url: '/api/v3/user/emails',
      emojis_url: '/api/v3/emojis',
      events_url: '/api/v3/events',
      feeds_url: '/api/v3/feeds',
      followers_url: '/api/v3/user/followers',
      following_url: '/api/v3/user/following{/target}',
      gists_url: '/api/v3/gists{/gist_id}',
      hub_url: 'https://api.github.com/hub',
      issue_search_url: '/api/v3/search/issues?q={query}{&page,per_page,sort,order}',
      issues_url: '/api/v3/issues',
      keys_url: '/api/v3/user/keys',
      label_search_url: '/api/v3/search/labels?q={query}&repository_id={repository_id}{&page,per_page}',
      notifications_url: '/api/v3/notifications{?since,all,participating}',
      organization_url: '/api/v3/orgs/{org}',
      public_gists_url: '/api/v3/gists/public',
      rate_limit_url: '/api/v3/rate_limit',
      repository_url: '/api/v3/repos/{owner}/{repo}',
      repository_search_url: '/api/v3/search/repositories?q={query}{&page,per_page,sort,order}',
      current_user_repositories_url: '/api/v3/user/repos{?type,page,per_page,sort}',
      starred_url: '/api/v3/user/starred{/owner}{/repo}',
      starred_gists_url: '/api/v3/gists/starred',
      topic_search_url: '/api/v3/search/topics?q={query}{&page,per_page}',
      user_url: '/api/v3/users/{user}',
      user_organizations_url: '/api/v3/user/orgs',
      user_repositories_url: '/api/v3/user/repos{?type,page,per_page,sort}',
      user_search_url: '/api/v3/search/users?q={query}{&page,per_page,sort,order}',
    }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }
  if (m === 'GET' && rest === '/meta') {
    sendJson(ctx.res, 200, {
      verifiable_password_authentication: false,
      github_services_sha: '0000000000000000000000000000000000000000',
      hooks: ['127.0.0.1/32'],
      git: ['127.0.0.1/32'],
      pages: ['127.0.0.1/32'],
      importer: ['127.0.0.1/32'],
      actions: ['127.0.0.1/32'],
      dependabot: ['127.0.0.1/32'],
      installed_version: '1.0.0',
    });
    return true;
  }

  if (!needAuth(ctx)) return true;

  const segs = rest.split('/').filter((s) => s !== '');
  const dec = (s: string): string => { try { return decodeURIComponent(s); } catch { return s; } };

  // GET /user
  if (m === 'GET' && rest === '/user') {
    sendJson(ctx.res, 200, {
      login: VIEWER_LOGIN, id: VIEWER_ID, node_id: globalId('User', VIEWER_ID),
      avatar_url: '', gravatar_id: '', url: '/api/v3/users/adaiversen',
      html_url: `https://github.com/${VIEWER_LOGIN}`, type: 'User', site_admin: false,
      name: VIEWER_NAME, company: null, blog: '', location: null, email: VIEWER_EMAIL,
      hireable: null, bio: null, twitter_username: null, public_repos: viewerRepos().length,
      public_gists: 0, followers: 0, following: 0, created_at: isoOf(0), updated_at: isoOf(0),
    });
    return true;
  }

  // /user/repos
  if (segs[0] === 'user' && segs[1] === 'repos') {
    if (m === 'GET') {
      sendPage(ctx, viewerRepos().map(repoJson));
      return true;
    }
    if (m === 'POST') {
      const body = await readJsonBody(ctx);
      if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
      if (!isRecord(body.value) || typeof body.value.name !== 'string' || body.value.name === '') {
        errJson(ctx.res, 422, 'Validation Failed: name is required');
        return true;
      }
      const name = body.value.name as string;
      if (getRepo(VIEWER_LOGIN, name)) {
        errJson(ctx.res, 422, `Repository ${VIEWER_LOGIN}/${name} already exists`);
        return true;
      }
      const repo = createRepoRecord(name, typeof body.value.description === 'string' ? body.value.description : '', body.value.private === true);
      sendJson(ctx.res, 201, repoJson(repo));
      return true;
    }
  }

  // /repos/{owner}/{repo}/...
  if (segs[0] === 'repos' && segs.length >= 3) {
    const owner = dec(segs[1]!);
    const name = dec(segs[2]!);
    const repo = getRepo(owner, name);
    const tail = segs.slice(3);

    if (owner !== VIEWER_LOGIN) {
      // A repository belongs to the login the token names; any other owner is 404.
      errJson(ctx.res, 404, 'Not Found');
      return true;
    }
    if (!repo) {
      errJson(ctx.res, 404, 'Not Found');
      return true;
    }

    // GET / PATCH / DELETE repo itself
    if (tail.length === 0) {
      if (m === 'GET') { sendJson(ctx.res, 200, repoJson(repo)); return true; }
      if (m === 'PATCH') {
        const body = await readJsonBody(ctx);
        if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
        if (isRecord(body.value)) {
          if (typeof body.value.description === 'string') repo.description = body.value.description;
          if (typeof body.value.private === 'boolean') repo.priv = body.value.private;
          if (typeof body.value.default_branch === 'string') repo.defaultBranch = body.value.default_branch;
        }
        sendJson(ctx.res, 200, repoJson(repo));
        return true;
      }
      if (m === 'DELETE') {
        repos.delete(repoKey(owner, name));
        ctx.res.writeHead(204, { 'x-github-request-id': `req-${++reqCounter}` });
        ctx.res.end();
        return true;
      }
    }

    // branches
    if (tail[0] === 'branches') {
      if (m === 'GET' && tail.length === 1) {
        const list = [...repo.refs.keys()]
          .filter((r) => r.startsWith('refs/heads/'))
          .sort()
          .map((r) => {
            const branch = r.slice('refs/heads/'.length);
            return { name: branch, commit: { sha: repo.refs.get(r), url: `/api/v3/repos/${owner}/${name}/commits/${repo.refs.get(r)}` }, protected: false };
          });
        sendJson(ctx.res, 200, list);
        return true;
      }
      if (m === 'GET' && tail.length === 2) {
        const branch = dec(tail[1]!);
        const tip = refTip(repo, branch);
        if (!tip) { errJson(ctx.res, 404, 'Not Found'); return true; }
        sendJson(ctx.res, 200, { name: branch, commit: { sha: tip, url: `/api/v3/repos/${owner}/${name}/commits/${tip}` }, protected: false });
        return true;
      }
    }

    // commits
    if (tail[0] === 'commits') {
      if (m === 'GET' && tail.length === 1) {
        const shaParam = ctx.query.get('sha');
        let tip: string | undefined;
        if (shaParam) {
          tip = repo.refs.get(`refs/heads/${shaParam}`) ?? (isOid(shaParam) ? shaParam : undefined);
          if (!tip) tip = repo.refs.get(shaParam);
        } else {
          tip = refTip(repo, repo.defaultBranch);
        }
        if (!tip || !repo.objects.has(tip)) { sendJson(ctx.res, 200, []); return true; }
        const commits = reachableCommits(repo, [tip]).map((oid) => commitJson(repo, oid));
        sendPage(ctx, commits);
        return true;
      }
      if (m === 'GET' && tail.length === 2) {
        const oid = dec(tail[1]!);
        if (!repo.objects.has(oid)) { errJson(ctx.res, 404, 'Not Found'); return true; }
        sendJson(ctx.res, 200, commitJson(repo, oid));
        return true;
      }
    }

    // git/refs
    if (tail[0] === 'git' && tail[1] === 'refs') {
      if (m === 'POST' && tail.length === 2) {
        const body = await readJsonBody(ctx);
        if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
        if (!isRecord(body.value) || typeof body.value.ref !== 'string' || typeof body.value.sha !== 'string') {
          errJson(ctx.res, 422, 'Validation Failed');
          return true;
        }
        const ref = body.value.ref as string;
        const sha = body.value.sha as string;
        if (!repo.objects.has(sha) || repo.objects.get(sha)!.type !== 'commit') {
          errJson(ctx.res, 422, 'Object does not exist');
          return true;
        }
        repo.refs.set(ref, sha);
        sendJson(ctx.res, 201, {
          ref, node_id: globalId('Ref', repo.id, ref),
          url: `/api/v3/repos/${owner}/${name}/git/refs/${encodeURIComponent(ref)}`,
          object: { sha, type: 'commit', url: `/api/v3/repos/${owner}/${name}/git/commits/${sha}` },
        });
        return true;
      }
      if (m === 'GET') {
        const refPath = tail.slice(2).map(dec).join('/');
        if (refPath === '') {
          const list = [...repo.refs.entries()].sort().map(([ref, sha]) => ({
            ref, node_id: globalId('Ref', repo.id, ref),
            url: `/api/v3/repos/${owner}/${name}/git/refs/${encodeURIComponent(ref)}`,
            object: { sha, type: 'commit', url: `/api/v3/repos/${owner}/${name}/git/commits/${sha}` },
          }));
          sendJson(ctx.res, 200, list);
          return true;
        }
        const sha = repo.refs.get(refPath);
        if (!sha) { errJson(ctx.res, 404, 'Not Found'); return true; }
        sendJson(ctx.res, 200, {
          ref: refPath, node_id: globalId('Ref', repo.id, refPath),
          url: `/api/v3/repos/${owner}/${name}/git/refs/${encodeURIComponent(refPath)}`,
          object: { sha, type: 'commit', url: `/api/v3/repos/${owner}/${name}/git/commits/${sha}` },
        });
        return true;
      }
    }

    // contents
    if (tail[0] === 'contents') {
      const filePath = tail.slice(1).map(dec).join('/');
      const refParam = ctx.query.get('ref');
      const branch = refParam ?? repo.defaultBranch;
      const tip = refTip(repo, branch);
      if (m === 'GET') {
        if (!tip) { errJson(ctx.res, 404, 'Not Found'); return true; }
        const tree = parseCommit(repo.objects.get(tip)!.data).tree;
        const files = flattenTree(repo, tree);
        if (filePath === '') {
          const entries = [...files.entries()].filter(([p]) => !p.includes('/')).map(([p, v]) => ({
            type: 'file', name: p, path: p, sha: v.oid, size: repo.objects.get(v.oid)?.data.length ?? 0,
            url: `/api/v3/repos/${owner}/${name}/contents/${encodeURIComponent(p)}`,
            html_url: `https://github.com/${owner}/${name}/blob/${branch}/${p}`,
            git_url: `/api/v3/repos/${owner}/${name}/git/blobs/${v.oid}`,
            download_url: null, _links: {},
          }));
          sendJson(ctx.res, 200, entries);
          return true;
        }
        const entry = files.get(filePath);
        if (entry) {
          const data = repo.objects.get(entry.oid)?.data ?? Buffer.alloc(0);
          sendJson(ctx.res, 200, {
            type: 'file', encoding: 'base64', size: data.length, name: filePath.split('/').pop(),
            path: filePath, content: b64encode(data), sha: entry.oid,
            url: `/api/v3/repos/${owner}/${name}/contents/${encodeURIComponent(filePath)}`,
            html_url: `https://github.com/${owner}/${name}/blob/${branch}/${filePath}`,
            git_url: `/api/v3/repos/${owner}/${name}/git/blobs/${entry.oid}`,
            download_url: null, _links: {},
          });
          return true;
        }
        // directory?
        const prefix = `${filePath}/`;
        const children = new Map<string, { oid: string; mode: string }>();
        for (const [p, v] of files) {
          if (p.startsWith(prefix)) {
            const rest = p.slice(prefix.length);
            const first = rest.split('/')[0]!;
            if (!children.has(first)) children.set(first, rest.includes('/') ? { oid: '', mode: '40000' } : v);
          }
        }
        if (children.size > 0) {
          const entries = [...children.entries()].sort().map(([childName, v]) => {
            const isDir = v.mode === '40000';
            const childPath = `${filePath}/${childName}`;
            return {
              type: isDir ? 'dir' : 'file', name: childName, path: childPath,
              sha: v.oid, size: isDir ? 0 : (repo.objects.get(v.oid)?.data.length ?? 0),
              url: `/api/v3/repos/${owner}/${name}/contents/${encodeURIComponent(childPath)}`,
              html_url: `https://github.com/${owner}/${name}/blob/${branch}/${childPath}`,
              git_url: `/api/v3/repos/${owner}/${name}/git/blobs/${v.oid}`,
              download_url: null, _links: {},
            };
          });
          sendJson(ctx.res, 200, entries);
          return true;
        }
        errJson(ctx.res, 404, 'Not Found');
        return true;
      }
      if (m === 'PUT') {
        const body = await readJsonBody(ctx);
        if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
        if (!isRecord(body.value) || typeof body.value.content !== 'string' || typeof body.value.message !== 'string') {
          errJson(ctx.res, 422, 'Validation Failed');
          return true;
        }
        const putBranch = typeof body.value.branch === 'string' ? body.value.branch : repo.defaultBranch;
        if (refTip(repo, putBranch) === undefined && repo.refs.size > 0 && !repo.refs.has(`refs/heads/${putBranch}`)) {
          errJson(ctx.res, 404, 'Not Found');
          return true;
        }
        const content = b64decode(body.value.content);
        const tipNow = refTip(repo, putBranch);
        const existed = tipNow !== undefined && flattenTree(repo, parseCommit(repo.objects.get(tipNow)!.data).tree).has(filePath);
        if (existed && typeof body.value.sha === 'string') {
          const current = flattenTree(repo, parseCommit(repo.objects.get(tipNow!)!.data).tree).get(filePath)!;
          if (body.value.sha !== current.oid) { errJson(ctx.res, 409, 'sha does not match'); return true; }
        }
        const { commitSha, blobSha } = commitFile(repo, putBranch, filePath, content, body.value.message);
        sendJson(ctx.res, existed ? 200 : 201, {
          content: { name: filePath.split('/').pop(), path: filePath, sha: blobSha, size: content.length, url: '', html_url: '', git_url: '', download_url: null, type: 'file', encoding: 'base64', _links: {} },
          commit: { sha: commitSha, node_id: globalId('Commit', repo.id, commitSha), url: '', html_url: '', author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: isoOf(seq) }, committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: isoOf(seq) }, message: body.value.message, tree: { sha: '', url: '' }, parents: [] },
        });
        return true;
      }
      if (m === 'DELETE') {
        const body = await readJsonBody(ctx);
        if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
        const delBranch = isRecord(body.value) && typeof body.value.branch === 'string' ? body.value.branch : repo.defaultBranch;
        const tipNow = refTip(repo, delBranch);
        if (!tipNow) { errJson(ctx.res, 404, 'Not Found'); return true; }
        const files = flattenTree(repo, parseCommit(repo.objects.get(tipNow)!.data).tree);
        if (!files.has(filePath)) { errJson(ctx.res, 404, 'Not Found'); return true; }
        const message = isRecord(body.value) && typeof body.value.message === 'string' ? body.value.message : `Delete ${filePath}`;
        const { commitSha } = commitFile(repo, delBranch, filePath, null, message);
        sendJson(ctx.res, 200, { commit: { sha: commitSha, node_id: globalId('Commit', repo.id, commitSha), url: '', html_url: '', message, tree: { sha: '', url: '' }, parents: [] }, content: null });
        return true;
      }
    }

    // labels
    if (tail[0] === 'labels') {
      if (m === 'POST' && tail.length === 1) {
        const body = await readJsonBody(ctx);
        if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
        if (!isRecord(body.value) || typeof body.value.name !== 'string' || body.value.name === '') {
          errJson(ctx.res, 422, 'Validation Failed');
          return true;
        }
        const label: Label = { name: body.value.name, color: typeof body.value.color === 'string' ? body.value.color : 'ededed' };
        repo.labels.set(label.name, label);
        sendJson(ctx.res, 201, { id: nextGlobalId++, node_id: globalId('Label', repo.id, label.name), url: '', name: label.name, color: label.color, default: false, description: '' });
        return true;
      }
      if (m === 'GET' && tail.length === 1) {
        sendJson(ctx.res, 200, [...repo.labels.values()].map((l) => ({ id: nextGlobalId++, node_id: globalId('Label', repo.id, l.name), name: l.name, color: l.color, default: false, description: '' })));
        return true;
      }
    }

    // issues
    if (tail[0] === 'issues') {
      if (tail.length === 1) {
        if (m === 'GET') {
          const state = ctx.query.get('state') ?? 'open';
          const sort = ctx.query.get('sort') ?? 'created';
          const direction = ctx.query.get('direction') ?? 'desc';
          let list = repo.issues.filter((i) => state === 'all' || i.state === state);
          list = [...list].sort((a, b) => {
            const cmp = sort === 'created' ? a.number - b.number : a.number - b.number;
            return direction === 'asc' ? cmp : -cmp;
          });
          sendPage(ctx, list.map((i) => issueJson(repo, i)));
          return true;
        }
        if (m === 'POST') {
          const body = await readJsonBody(ctx);
          if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
          if (!isRecord(body.value) || typeof body.value.title !== 'string') {
            errJson(ctx.res, 422, 'Validation Failed');
            return true;
          }
          const labelsRaw = Array.isArray(body.value.labels) ? body.value.labels : [];
          const labels: Label[] = [];
          for (const l of labelsRaw) {
            const lname = typeof l === 'string' ? l : isRecord(l) ? String(l.name ?? '') : '';
            const found = repo.labels.get(lname);
            if (!found) { errJson(ctx.res, 422, `Validation Failed: label ${lname} does not exist`); return true; }
            labels.push(found);
          }
          const issue: Issue = {
            id: nextGlobalId++, number: repo.nextIssue++, title: body.value.title,
            body: typeof body.value.body === 'string' ? body.value.body : '',
            state: 'open', labels, user: VIEWER_LOGIN, createdSeq: ++seq, comments: [],
            jsonCache: null,
          };
          repo.issues.push(issue);
          sendIssue(ctx, 201, repo, issue);
          return true;
        }
      }
      const num = Number(tail[1]);
      const issue = Number.isInteger(num) ? repo.issues.find((i) => i.number === num) : undefined;
      if (tail.length === 2) {
        if (!issue) { errJson(ctx.res, 404, 'Not Found'); return true; }
        if (m === 'GET') { sendIssue(ctx, 200, repo, issue); return true; }
        if (m === 'PATCH') {
          const body = await readJsonBody(ctx);
          if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
          if (isRecord(body.value)) {
            if (body.value.state === 'open' || body.value.state === 'closed') issue.state = body.value.state;
            if (typeof body.value.title === 'string') issue.title = body.value.title;
            if (typeof body.value.body === 'string') issue.body = body.value.body;
          }
          invalidateIssue(issue);
          sendIssue(ctx, 200, repo, issue);
          return true;
        }
      }
      if (tail[2] === 'comments' && issue) {
        if (m === 'GET') {
          sendJson(ctx.res, 200, issue.comments.map((c) => ({
            id: c.id, node_id: globalId('IssueComment', repo.id, issue.number, c.id),
            url: '', html_url: '', body: c.body,
            user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
            created_at: isoOf(c.createdSeq), updated_at: isoOf(c.createdSeq),
          })));
          return true;
        }
        if (m === 'POST') {
          const body = await readJsonBody(ctx);
          if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
          if (!isRecord(body.value) || typeof body.value.body !== 'string') {
            errJson(ctx.res, 422, 'Validation Failed');
            return true;
          }
          const comment: Comment = { id: repo.nextComment++, body: body.value.body, user: VIEWER_LOGIN, createdSeq: ++seq };
          issue.comments.push(comment);
          invalidateIssue(issue);
          sendJson(ctx.res, 201, {
            id: comment.id, node_id: globalId('IssueComment', repo.id, issue.number, comment.id),
            url: '', html_url: '', body: comment.body,
            user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
            created_at: isoOf(comment.createdSeq), updated_at: isoOf(comment.createdSeq),
          });
          return true;
        }
      }
      if (tail.length >= 2 && !issue) { errJson(ctx.res, 404, 'Not Found'); return true; }
    }

    // pulls
    if (tail[0] === 'pulls') {
      if (tail.length === 1) {
        if (m === 'GET') {
          const state = ctx.query.get('state') ?? 'open';
          const list = repo.pulls.filter((pr) => state === 'all' || pr.state === state);
          sendPage(ctx, list.map((pr) => pullJson(repo, pr)));
          return true;
        }
        if (m === 'POST') {
          const body = await readJsonBody(ctx);
          if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
          if (!isRecord(body.value) || typeof body.value.head !== 'string' || typeof body.value.base !== 'string') {
            errJson(ctx.res, 422, 'Validation Failed');
            return true;
          }
          const headSha = refTip(repo, body.value.head);
          const baseSha = refTip(repo, body.value.base);
          if (!headSha || !baseSha) { errJson(ctx.res, 422, 'Validation Failed: head or base branch does not exist'); return true; }
          const pr: Pull = {
            id: nextGlobalId++, number: repo.nextPull++,
            title: typeof body.value.title === 'string' ? body.value.title : '',
            body: typeof body.value.body === 'string' ? body.value.body : '',
            state: 'open', head: body.value.head, base: body.value.base,
            headSha, baseSha, merged: false, mergedAt: null, mergeCommitSha: null, createdSeq: ++seq,
          };
          repo.pulls.push(pr);
          sendJson(ctx.res, 201, pullJson(repo, pr));
          return true;
        }
      }
      const num = Number(tail[1]);
      const pr = Number.isInteger(num) ? repo.pulls.find((p) => p.number === num) : undefined;
      if (tail.length === 2) {
        if (!pr) { errJson(ctx.res, 404, 'Not Found'); return true; }
        if (m === 'GET') { sendJson(ctx.res, 200, pullJson(repo, pr)); return true; }
        if (m === 'PATCH') {
          const body = await readJsonBody(ctx);
          if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
          if (isRecord(body.value)) {
            if (body.value.state === 'closed') pr.state = 'closed';
            if (typeof body.value.title === 'string') pr.title = body.value.title;
            if (typeof body.value.body === 'string') pr.body = body.value.body;
          }
          sendJson(ctx.res, 200, pullJson(repo, pr));
          return true;
        }
      }
      if (tail.length === 3 && tail[2] === 'files' && m === 'GET') {
        if (!pr) { errJson(ctx.res, 404, 'Not Found'); return true; }
        const baseTree = parseCommit(repo.objects.get(pr.baseSha)!.data).tree;
        const headTree = parseCommit(repo.objects.get(pr.headSha)!.data).tree;
        sendJson(ctx.res, 200, diffFiles(repo, baseTree, headTree));
        return true;
      }
      if (tail.length === 3 && tail[2] === 'merge' && m === 'PUT') {
        if (!pr) { errJson(ctx.res, 404, 'Not Found'); return true; }
        if (pr.state !== 'open') { errJson(ctx.res, 405, 'Pull request is already closed'); return true; }
        const result = squashMerge(repo, pr);
        if (result.conflict) { errJson(ctx.res, 405, 'Merge conflict'); return true; }
        if (!result.ok) { errJson(ctx.res, 405, 'Merge failed'); return true; }
        // Drain the body (merge_method) if present.
        await readBody(ctx.req).catch(() => undefined);
        sendJson(ctx.res, 200, { sha: result.sha, merged: true, message: `Pull request #${pr.number} successfully merged` });
        return true;
      }
      if (!pr) { errJson(ctx.res, 404, 'Not Found'); return true; }
    }

    errJson(ctx.res, 404, 'Not Found');
    return true;
  }

  errJson(ctx.res, 404, 'Not Found');
  return true;
}

// ---------------------------------------------------------------------------
// git smart HTTP

function gitRefsList(repo: Repo): Array<{ oid: string; name: string; peeled?: string }> {
  const out: Array<{ oid: string; name: string; peeled?: string }> = [];
  const sorted = [...repo.refs.entries()].sort(([a], [b]) => (a < b ? -1 : 1));
  for (const [name, oid] of sorted) {
    out.push({ oid, name });
    const obj = repo.objects.get(oid);
    if (obj && obj.type === 'tag') {
      const target = parseTag(obj.data).object;
      out.push({ oid: target, name: `${name}^{}` });
    }
  }
  return out;
}

function defaultBranchTip(repo: Repo): string | undefined {
  return refTip(repo, repo.defaultBranch);
}

function v0Advertisement(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps = service === 'git-upload-pack'
    ? 'side-band-64k thin-pack ofs-delta multi_ack symref=HEAD:refs/heads/main agent=github-forge/1.0.0 shallow'
    : 'report-status report-status-v2 side-band-64k delete-refs ofs-delta agent=github-forge/1.0.0';
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const refs = gitRefsList(repo);
  const headTip = defaultBranchTip(repo);
  const lines: Array<{ oid: string; name: string }> = [];
  if (headTip) lines.push({ oid: headTip, name: 'HEAD' });
  for (const r of refs) lines.push(r);
  if (lines.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    lines.forEach((r, i) => {
      parts.push(pktLine(i === 0 ? `${r.oid} ${r.name}\0${caps}\n` : `${r.oid} ${r.name}\n`));
    });
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

const V2_ADVERTISEMENT: Buffer = Buffer.concat([
  ...[
    'version 2\n',
    'agent=github-forge/1.0.0\n',
    'ls-refs=unborn\n',
    'fetch=shallow wait-for-done filter\n',
    'server-option\n',
    'object-format=sha1\n',
    'object-info\n',
  ].map((l) => pktLine(l)),
  PKT_FLUSH,
]);

/** Refs snapshot: sorted `name=oid` pairs. A fetch/advertisement response is a
 *  pure function of the refs, the object count and the request, so this plus
 *  the request args is an exact cache key (objects only ever grow). */
function refsFingerprint(repo: Repo): string {
  return [...repo.refs.entries()].sort(([a], [b]) => (a < b ? -1 : 1)).map(([n, o]) => `${n}=${o}`).join(',');
}

/** Bounded cache put (FIFO eviction, keeps the newest 16 entries). */
function cachePut(cache: Map<string, Buffer>, key: string, value: Buffer): void {
  if (cache.size >= 16) {
    const first = cache.keys().next().value;
    if (first !== undefined) cache.delete(first);
  }
  cache.set(key, value);
}

function sidebandPack(pack: Buffer, chunkSize = 65500): Buffer[] {
  const out: Buffer[] = [];
  for (let i = 0; i < pack.length; i += chunkSize) {
    const chunk = pack.subarray(i, Math.min(pack.length, i + chunkSize));
    out.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  return out;
}

interface FetchPlan {
  commits: string[]; // commits to send (generation order)
  objects: GitObject[];
  shallow: string[];
  unshallow: string[];
}

/** Compute what a fetch sends: BFS from wants, depth-limited, minus haves' closure. */
function planFetch(repo: Repo, wants: string[], haves: string[], depth: number | null, clientShallow: string[]): FetchPlan {
  const haveSet = new Set<string>();
  if (haves.length > 0) {
    // Object closure of the haves: every commit, tree, subtree and blob
    // reachable from them, so an incremental fetch never re-sends held
    // objects. A have that is one of the client's shallow boundaries holds
    // only its own objects: the walk stops there (a deepen extends past it),
    // so its ancestors are NOT treated as held.
    const shallowSet = new Set(clientShallow);
    const hc: string[] = [];
    {
      const seen = new Set<string>();
      const queue = [...haves];
      let head = 0;
      while (head < queue.length) {
        const oid = queue[head++]!;
        if (seen.has(oid)) continue;
        seen.add(oid);
        const obj = repo.objects.get(oid);
        if (!obj || obj.type !== 'commit') continue;
        hc.push(oid);
        if (shallowSet.has(oid)) continue;
        for (const p of parseCommit(obj.data).parents) queue.push(p);
      }
    }
    for (const c of hc) haveSet.add(c);
    const walkTree = (treeOid: string): void => {
      if (haveSet.has(treeOid)) return;
      haveSet.add(treeOid);
      const obj = repo.objects.get(treeOid);
      if (!obj || obj.type !== 'tree') return;
      for (const e of parseTree(obj.data)) {
        if (e.mode === '40000') walkTree(e.oid);
        else haveSet.add(e.oid);
      }
    };
    for (const c of hc) {
      const obj = repo.objects.get(c);
      if (!obj) continue;
      walkTree(parseCommit(obj.data).tree);
    }
    for (const h of haves) {
      const obj = repo.objects.get(h);
      if (obj && obj.type === 'tag') {
        haveSet.add(h);
        const target = parseTag(obj.data).object;
        const t = repo.objects.get(target);
        if (t && t.type === 'commit') {
          for (const cc of reachableCommits(repo, [target])) {
            haveSet.add(cc);
            const co = repo.objects.get(cc);
            if (co) walkTree(parseCommit(co.data).tree);
          }
        }
      }
    }
  }
  // BFS generations from wants
  const gen = new Map<string, number>();
  const queue: string[] = [];
  for (const w of wants) {
    if (repo.objects.has(w) && repo.objects.get(w)!.type === 'commit' && !gen.has(w)) {
      gen.set(w, 0);
      queue.push(w);
    }
  }
  const commits: string[] = [];
  const shallow: string[] = [];
  let qhead = 0;
  while (qhead < queue.length) {
    const oid = queue[qhead++]!;
    const g = gen.get(oid)!;
    commits.push(oid);
    const parents = commitParents(repo, oid);
    const atLimit = depth !== null && g + 1 >= depth;
    if (atLimit) shallow.push(oid);
    if (depth === null || g + 1 < depth) {
      for (const p of parents) {
        if (!gen.has(p) && repo.objects.has(p)) { gen.set(p, g + 1); queue.push(p); }
      }
    }
  }
  const unshallow = clientShallow.filter((s) => gen.has(s) && !shallow.includes(s));
  // Objects reachable from the planned commits, minus haves' closure.
  const send = new Map<string, GitObject>();
  for (const c of commits) {
    if (haveSet.has(c)) continue;
    const obj = repo.objects.get(c);
    if (!obj) continue;
    send.set(c, obj);
    const tree = parseCommit(obj.data).tree;
    const collect = (treeOid: string): void => {
      if (haveSet.has(treeOid)) return;
      const tobj = repo.objects.get(treeOid);
      if (!tobj || tobj.type !== 'tree') return;
      send.set(treeOid, tobj);
      for (const e of parseTree(tobj.data)) {
        if (e.mode === '40000') collect(e.oid);
        else if (!haveSet.has(e.oid)) {
          const b = repo.objects.get(e.oid);
          if (b) send.set(e.oid, b);
        }
      }
    };
    collect(tree);
  }
  // Tag objects pointing at wanted commits/tags: include tags whose target is sent.
  for (const [name, oid] of repo.refs) {
    if (!name.startsWith('refs/tags/')) continue;
    const obj = repo.objects.get(oid);
    if (obj && obj.type === 'tag' && send.has(parseTag(obj.data).object) && !haveSet.has(oid)) {
      send.set(oid, obj);
    }
  }
  const objects = [...send.entries()].sort(([a], [b]) => (a < b ? -1 : 1)).map(([, o]) => o);
  return { commits, objects, shallow, unshallow };
}

function parseV2FetchArgs(lines: string[]): { wants: string[]; haves: string[]; depth: number | null; shallow: string[]; filter?: string } {
  const wants: string[] = [];
  const haves: string[] = [];
  const shallow: string[] = [];
  let depth: number | null = null;
  let filter: string | undefined;
  for (const line of lines) {
    const t = line.replace(/\n$/, '');
    if (t.startsWith('want ')) wants.push(t.slice(5).trim());
    else if (t.startsWith('have ')) haves.push(t.slice(5).trim());
    else if (t.startsWith('shallow ')) shallow.push(t.slice(8).trim());
    else if (t.startsWith('deepen ')) depth = Number(t.slice(7).trim());
    else if (t.startsWith('deepen-since ')) depth = 1;
    else if (t.startsWith('filter ')) filter = t.slice(7).trim();
  }
  return { wants, haves, depth, shallow, filter };
}

async function handleGitUploadPack(ctx: Ctx, repo: Repo, body: Buffer): Promise<void> {
  const isV2 = (ctx.req.headers['git-protocol'] ?? '') === 'version=2';
  let packets: Pkt[];
  try {
    packets = decodePktLines(body);
  } catch {
    errJson(ctx.res, 400, 'bad pkt-line');
    return;
  }
  const dataLines = packets.filter((p) => p.kind === 'data').map((p) => p.payload.toString('utf8'));
  if (isV2) {
    const command = dataLines.find((l) => l.startsWith('command='))?.slice(8).trim() ?? '';
    if (command === 'ls-refs') {
      const prefixes: string[] = [];
      let peel = false;
      let symrefs = false;
      for (const l of dataLines) {
        const t = l.replace(/\n$/, '');
        if (t.startsWith('ref-prefix ')) prefixes.push(t.slice(11));
        else if (t === 'peel') peel = true;
        else if (t === 'symrefs') symrefs = true;
      }
      // ls-refs is a pure function of the refs + the three flags: cache it.
      const lsKey = `ls:${refsFingerprint(repo)}:${prefixes.join(',')}:${peel}:${symrefs}`;
      const cachedLs = repo.packCache.get(lsKey);
      if (cachedLs) {
        sendRaw(ctx.res, 200, cachedLs, 'application/x-git-upload-pack-result');
        return;
      }
      const parts: Buffer[] = [];
      const headTip = defaultBranchTip(repo);
      const headAllowed = prefixes.length === 0 || prefixes.some((pre) => 'HEAD'.startsWith(pre));
      if (headAllowed) {
        if (headTip) {
          parts.push(pktLine(`${headTip} HEAD symref-target:refs/heads/${repo.defaultBranch}\n`));
        } else {
          parts.push(pktLine(`unborn HEAD symref-target:refs/heads/${repo.defaultBranch}\n`));
        }
      }
      for (const r of gitRefsList(repo)) {
        if (prefixes.length > 0 && !prefixes.some((pre) => r.name.startsWith(pre))) continue;
        if (r.name.endsWith('^{}')) continue;
        let line = `${r.oid} ${r.name}`;
        if (peel) {
          const obj = repo.objects.get(r.oid);
          if (obj && obj.type === 'tag') line += ` peeled:${parseTag(obj.data).object}`;
        }
        if (symrefs && r.name === `refs/heads/${repo.defaultBranch}`) line += ` symref-target:refs/heads/${repo.defaultBranch}`;
        parts.push(pktLine(`${line}\n`));
      }
      parts.push(PKT_FLUSH);
      const lsBody = Buffer.concat(parts);
      cachePut(repo.packCache, lsKey, lsBody);
      sendRaw(ctx.res, 200, lsBody, 'application/x-git-upload-pack-result');
      return;
    }
    if (command === 'fetch') {
      const args = parseV2FetchArgs(dataLines);
      // The whole fetch response (acks + shallow lines + pack) is a pure
      // function of the request args + refs + object set: cache it, so 50
      // identical shallow clones share one planFetch + writePack.
      const fetchKey = `f2:${refsFingerprint(repo)}:${repo.objects.size}:${args.wants.join(',')}:${args.haves.join(',')}:${args.depth}:${args.shallow.join(',')}:${args.filter ?? ''}`;
      const cachedFetch = repo.packCache.get(fetchKey);
      if (cachedFetch) {
        sendRaw(ctx.res, 200, cachedFetch, 'application/x-git-upload-pack-result');
        return;
      }
      const plan = planFetch(repo, args.wants, args.haves, args.depth, args.shallow);
      const pack = writePack(plan.objects);
      const parts: Buffer[] = [];
      parts.push(pktLine('acknowledgments\n'));
      if (args.haves.length === 0) parts.push(pktLine('NAK\n'));
      else {
        for (const h of args.haves) if (repo.objects.has(h)) parts.push(pktLine(`ACK ${h}\n`));
        parts.push(pktLine('ready\n'));
      }
      parts.push(PKT_DELIM);
      if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
        parts.push(pktLine('shallow-info\n'));
        for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
        for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
        parts.push(PKT_DELIM);
      }
      parts.push(pktLine('packfile\n'));
      for (const p of sidebandPack(pack)) parts.push(p);
      parts.push(PKT_FLUSH);
      const fetchBody = Buffer.concat(parts);
      cachePut(repo.packCache, fetchKey, fetchBody);
      sendRaw(ctx.res, 200, fetchBody, 'application/x-git-upload-pack-result');
      return;
    }
    errJson(ctx.res, 400, 'unknown v2 command');
    return;
  }
  // v0 fetch
  const wants: string[] = [];
  const haves: string[] = [];
  const shallowIn: string[] = [];
  let depth: number | null = null;
  let section = 0;
  for (const p of packets) {
    if (p.kind === 'flush') { section += 1; continue; }
    if (p.kind !== 'data') continue;
    const t = p.payload.toString('utf8').replace(/\n$/, '');
    if (section === 0) {
      if (t.startsWith('want ')) wants.push(t.slice(5).split(' ')[0]!);
      else if (t.startsWith('shallow ')) shallowIn.push(t.slice(8).trim());
      else if (t.startsWith('deepen ')) depth = Number(t.slice(7).trim());
    } else {
      if (t.startsWith('have ')) haves.push(t.slice(5).trim());
    }
  }
  const fetch0Key = `f0:${refsFingerprint(repo)}:${repo.objects.size}:${wants.join(',')}:${haves.join(',')}:${depth}:${shallowIn.join(',')}`;
  const cachedFetch0 = repo.packCache.get(fetch0Key);
  if (cachedFetch0) {
    sendRaw(ctx.res, 200, cachedFetch0, 'application/x-git-upload-pack-result');
    return;
  }
  const plan = planFetch(repo, wants, haves, depth, shallowIn);
  const pack = writePack(plan.objects);
  const parts: Buffer[] = [];
  if (haves.length === 0) parts.push(pktLine('NAK\n'));
  else {
    for (const h of haves) if (repo.objects.has(h)) parts.push(pktLine(`ACK ${h}\n`));
  }
  for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
  for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
  for (const p of sidebandPack(pack)) parts.push(p);
  parts.push(PKT_FLUSH);
  const fetch0Body = Buffer.concat(parts);
  cachePut(repo.packCache, fetch0Key, fetch0Body);
  sendRaw(ctx.res, 200, fetch0Body, 'application/x-git-upload-pack-result');
}

async function handleGitReceivePack(ctx: Ctx, repo: Repo, body: Buffer): Promise<void> {
  // Parse pkt-lines one at a time until the first flush; everything after
  // the flush is the packfile, which is binary and must not be pkt-decoded.
  const commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
  let offset = 0;
  let sawFlush = false;
  try {
    while (offset < body.length) {
      if (offset + 4 > body.length) throw new Error('truncated pkt-line header');
      const hex = body.subarray(offset, offset + 4).toString('ascii');
      if (hex === '0000') { offset += 4; sawFlush = true; break; }
      if (hex === '0001' || hex === '0002') { offset += 4; continue; }
      const len = parseInt(hex, 16);
      if (!Number.isFinite(len) || len < 4 || offset + len > body.length) throw new Error('bad pkt-line length');
      const payload = body.subarray(offset + 4, offset + len);
      let text = payload.toString('utf8');
      const nul = text.indexOf('\0');
      if (nul >= 0) text = text.slice(0, nul);
      const line = text.replace(/\n$/, '');
      const parts = line.split(' ');
      if (parts.length >= 3 && isOid(parts[0]!) && isOid(parts[1]!)) {
        commands.push({ oldOid: parts[0]!, newOid: parts[1]!, ref: parts.slice(2).join(' ') });
      }
      offset += len;
    }
  } catch {
    errJson(ctx.res, 400, 'bad pkt-line');
    return;
  }
  if (!sawFlush || commands.length === 0) {
    errJson(ctx.res, 400, 'no push commands');
    return;
  }
  const packBytes = body.subarray(offset);
  let incoming = new Map<string, GitObject>();
  let unpackOk = true;
  let unpackDetail = 'ok';
  const updates = commands.some((c) => c.newOid !== ZERO_OID);
  if (updates) {
    if (packBytes.length < 12) {
      unpackOk = false;
      unpackDetail = 'unpacker error: missing packfile';
    } else {
      try {
        incoming = readPack(Buffer.from(packBytes), (oid) => repo.objects.get(oid));
      } catch (e) {
        unpackOk = false;
        unpackDetail = `unpacker error: ${e instanceof Error ? e.message : String(e)}`;
      }
    }
  }
  const reportLines: string[] = [];
  if (unpackOk) {
    // Validate that every new tip's closure is present (incoming + existing).
    // Only objects the push itself brings need their closure walked: an
    // object already in the store had its closure validated when stored, so
    // the walk stops at it instead of re-walking the whole history per push.
    for (const cmd of commands) {
      if (cmd.newOid === ZERO_OID) continue;
      try {
        const missing = collectMissing(repo.objects, incoming, cmd.newOid);
        if (missing.length > 0) throw new Error(`missing object ${missing[0]}`);
      } catch (e) {
        unpackOk = false;
        unpackDetail = `unpacker error: ${e instanceof Error ? e.message : String(e)}`;
        break;
      }
    }
  }
  if (unpackOk) {
    for (const [oid, obj] of incoming) {
      if (!repo.objects.has(oid)) repo.objects.set(oid, obj);
    }
    for (const cmd of commands) {
      const current = repo.refs.get(cmd.ref);
      if (cmd.newOid === ZERO_OID) {
        // delete
        if (current === undefined) {
          reportLines.push(`ng ${cmd.ref} remote ref does not exist`);
        } else if (cmd.oldOid !== ZERO_OID && cmd.oldOid !== current) {
          reportLines.push(`ng ${cmd.ref} non-fast-forward`);
        } else {
          repo.refs.delete(cmd.ref);
          reportLines.push(`ok ${cmd.ref}`);
        }
        continue;
      }
      if (current === undefined) {
        if (cmd.oldOid !== ZERO_OID) {
          reportLines.push(`ng ${cmd.ref} non-fast-forward`);
          continue;
        }
        repo.refs.set(cmd.ref, cmd.newOid);
        reportLines.push(`ok ${cmd.ref}`);
        continue;
      }
      if (cmd.oldOid !== current) {
        reportLines.push(`ng ${cmd.ref} non-fast-forward`);
        continue;
      }
      if (!isAncestor(repo, current, cmd.newOid)) {
        reportLines.push(`ng ${cmd.ref} non-fast-forward`);
        continue;
      }
      repo.refs.set(cmd.ref, cmd.newOid);
      reportLines.push(`ok ${cmd.ref}`);
    }
  }
  const lines: string[] = [`unpack ${unpackOk ? 'ok' : unpackDetail}`];
  if (!unpackOk) {
    for (const cmd of commands) lines.push(`ng ${cmd.ref} unpack failed`);
  } else {
    lines.push(...reportLines);
  }
  const reportBody = Buffer.concat(lines.map((l) => pktLine(`${l}\n`)).concat([PKT_FLUSH]));
  const out: Buffer[] = [pktLine(Buffer.concat([Buffer.from([1]), reportBody]))];
  out.push(PKT_FLUSH);
  sendRaw(ctx.res, 200, Buffer.concat(out), 'application/x-git-receive-pack-result');
}

/**
 * Objects reachable from `root` that are in neither `existing` nor `incoming`.
 * Only `incoming` objects are descended into: an object already in `existing`
 * had its closure validated when it was stored, so its subtree is complete
 * by induction and re-walking it on every push is pure O(history) waste.
 */
function collectMissing(existing: Map<string, GitObject>, incoming: Map<string, GitObject>, root: string): string[] {
  const missing: string[] = [];
  const seen = new Set<string>();
  const get = (oid: string): GitObject | undefined => incoming.get(oid) ?? existing.get(oid);
  const visitCommit = (oid: string): void => {
    if (seen.has(oid)) return;
    seen.add(oid);
    const obj = get(oid);
    if (!obj) { missing.push(oid); return; }
    if (obj.type !== 'commit') return;
    if (!incoming.has(oid)) return; // pre-existing commit: closure complete
    const view = parseCommit(obj.data);
    visitTree(view.tree);
    for (const p of view.parents) visitCommit(p);
  };
  const visitTree = (oid: string): void => {
    if (seen.has(oid)) return;
    seen.add(oid);
    const obj = get(oid);
    if (!obj) { missing.push(oid); return; }
    if (obj.type !== 'tree') return;
    if (!incoming.has(oid)) return; // pre-existing tree: closure complete
    for (const e of parseTree(obj.data)) {
      if (e.mode === '40000') visitTree(e.oid);
      else if (!get(e.oid)) missing.push(e.oid);
    }
  };
  const rootObj = get(root);
  if (!rootObj) return [root];
  if (rootObj.type === 'commit') visitCommit(root);
  else if (rootObj.type === 'tree') visitTree(root);
  else if (rootObj.type === 'tag') {
    const target = parseTag(rootObj.data).object;
    const t = get(target);
    if (!t) missing.push(target);
    else if (t.type === 'commit') visitCommit(target);
  }
  return missing;
}

async function handleGit(ctx: Ctx): Promise<boolean> {
  const m = ctx.path.match(/^\/([^/]+)\/([^/]+)\.git\/(.*)$/);
  if (!m) return false;
  const owner = decodeURIComponent(m[1]!);
  const name = decodeURIComponent(m[2]!);
  const suffix = m[3]!;
  const repo = getRepo(owner, name);
  if (ctx.method === 'GET' && suffix.startsWith('info/refs')) {
    const service = ctx.query.get('service') as 'git-upload-pack' | 'git-receive-pack' | null;
    if (!repo) {
      sendJson(ctx.res, 404, { message: 'Not Found' });
      return true;
    }
    if (service === 'git-receive-pack') {
      const key = `recv:${refsFingerprint(repo)}`;
      let adv = repo.advCache.get(key);
      if (!adv) { adv = v0Advertisement(repo, 'git-receive-pack'); cachePut(repo.advCache, key, adv); }
      sendRaw(ctx.res, 200, adv, 'application/x-git-receive-pack-advertisement');
      return true;
    }
    if (service === 'git-upload-pack') {
      const isV2 = (ctx.req.headers['git-protocol'] ?? '') === 'version=2';
      if (isV2) {
        sendRaw(ctx.res, 200, V2_ADVERTISEMENT, 'application/x-git-upload-pack-advertisement');
      } else {
        const key = `up:${refsFingerprint(repo)}`;
        let adv = repo.advCache.get(key);
        if (!adv) { adv = v0Advertisement(repo, 'git-upload-pack'); cachePut(repo.advCache, key, adv); }
        sendRaw(ctx.res, 200, adv, 'application/x-git-upload-pack-advertisement');
      }
      return true;
    }
    errJson(ctx.res, 400, 'unknown service');
    return true;
  }
  if (ctx.method === 'POST' && suffix === 'git-upload-pack') {
    if (!repo) { sendJson(ctx.res, 404, { message: 'Not Found' }); return true; }
    const body = await readBody(ctx.req).catch(() => Buffer.alloc(0));
    await handleGitUploadPack(ctx, repo, body);
    return true;
  }
  if (ctx.method === 'POST' && suffix === 'git-receive-pack') {
    if (!repo) { sendJson(ctx.res, 404, { message: 'Not Found' }); return true; }
    const body = await readBody(ctx.req).catch(() => Buffer.alloc(0));
    await handleGitReceivePack(ctx, repo, body);
    return true;
  }
  return false;
}

// ---------------------------------------------------------------------------
// GraphQL v4

interface GqlField {
  alias: string | null;
  name: string;
  args: Record<string, unknown>;
  children: GqlField[];
  fragmentType: string | null;
}

interface GqlDoc {
  kind: 'query' | 'mutation';
  operationName: string | null;
  varDefs: Record<string, string>;
  fields: GqlField[];
}

function gqlTokenize(src: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i]!;
    if (/\s/.test(c) || c === ',') { i += 1; continue; }
    if (c === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (c === '.' && src.slice(i, i + 3) === '...') { tokens.push('...'); i += 3; continue; }
    if ('{}():!=$@[]'.includes(c)) { tokens.push(c); i += 1; continue; }
    if (c === '"') {
      let j = i + 1;
      let s = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) { s += src[j + 1]; j += 2; } else { s += src[j]; j += 1; }
      }
      tokens.push(JSON.stringify(s));
      i = j + 1;
      continue;
    }
    let j = i;
    while (j < src.length && /[A-Za-z0-9_]/.test(src[j]!)) j += 1;
    if (j === i) { i += 1; continue; }
    tokens.push(src.slice(i, j));
    i = j;
  }
  return tokens;
}

class GqlParser {
  tokens: string[];
  pos = 0;
  variables: Record<string, unknown>;
  constructor(src: string, variables: Record<string, unknown>) {
    this.tokens = gqlTokenize(src);
    this.variables = variables;
  }
  peek(): string | undefined { return this.tokens[this.pos]; }
  next(): string { return this.tokens[this.pos++]!; }
  expect(t: string): void {
    const got = this.next();
    if (got !== t) throw new Error(`expected ${t}, got ${got}`);
  }
  parseValue(): unknown {
    const t = this.peek();
    if (t === '$') {
      this.next();
      const name = this.next();
      return this.variables[name];
    }
    if (t === '{') {
      this.next();
      const obj: Record<string, unknown> = {};
      while (this.peek() !== '}') {
        const key = this.next();
        this.expect(':');
        obj[key!] = this.parseValue();
      }
      this.expect('}');
      return obj;
    }
    if (t === '[') {
      this.next();
      const arr: unknown[] = [];
      while (this.peek() !== ']') arr.push(this.parseValue());
      this.expect(']');
      return arr;
    }
    if (t === 'null') { this.next(); return null; }
    if (t === 'true') { this.next(); return true; }
    if (t === 'false') { this.next(); return false; }
    const tok = this.next()!;
    if (tok.startsWith('"')) return JSON.parse(tok);
    if (/^-?\d+$/.test(tok)) return Number(tok);
    if (/^-?\d+\.\d+$/.test(tok)) return Number(tok);
    return tok; // enum value as string
  }
  parseArgs(): Record<string, unknown> {
    const args: Record<string, unknown> = {};
    if (this.peek() !== '(') return args;
    this.next();
    while (this.peek() !== ')') {
      const name = this.next();
      this.expect(':');
      args[name!] = this.parseValue();
    }
    this.expect(')');
    return args;
  }
  parseSelectionSet(): GqlField[] {
    this.expect('{');
    const fields: GqlField[] = [];
    while (this.peek() !== '}') {
      fields.push(this.parseField());
    }
    this.expect('}');
    return fields;
  }
  parseField(): GqlField {
    let name = this.next()!;
    let alias: string | null = null;
    if (this.peek() === ':') {
      this.next();
      alias = name;
      name = this.next()!;
    }
    if (name === '...') {
      // fragment: `... on Type { ... }` or `...Fragment`
      if (this.peek() === 'on') {
        this.next();
        const typeName = this.next()!;
        const children = this.parseSelectionSet();
        return { alias: null, name: '...', args: {}, children, fragmentType: typeName };
      }
      const fragName = this.next()!;
      return { alias: null, name: `...${fragName}`, args: {}, children: [], fragmentType: null };
    }
    const args = this.parseArgs();
    let children: GqlField[] = [];
    if (this.peek() === '{') children = this.parseSelectionSet();
    return { alias, name, args, children, fragmentType: null };
  }
  parseDocument(): GqlDoc {
    let kind: 'query' | 'mutation' = 'query';
    let operationName: string | null = null;
    const first = this.peek();
    if (first === 'query' || first === 'mutation') {
      kind = first as 'query' | 'mutation';
      this.next();
      const nxt = this.peek();
      if (nxt !== undefined && nxt !== '(' && nxt !== '{') { operationName = this.next()!; }
      // variable definitions
      if (this.peek() === '(') {
        this.next();
        let depth = 1;
        while (depth > 0) {
          const t = this.next();
          if (t === '(' || t === '[' || t === '{') depth += 1;
          if (t === ')' || t === ']' || t === '}') depth -= 1;
        }
      }
    }
    const fields = this.parseSelectionSet();
    return { kind, operationName, varDefs: {}, fields };
  }
}

const ISSUE_TYPE_FIELDS = ['id', 'number', 'title', 'state', 'body', 'url', 'createdAt', 'updatedAt', 'author', 'labels', 'comments'];
const PR_TYPE_FIELDS = ['id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRef', 'baseRef', 'files', 'url', 'createdAt', 'mergedAt', 'mergeCommit', 'author'];
const REPO_TYPE_FIELDS = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'description', 'private', 'url', 'createdAt'];
const QUERY_TYPE_FIELDS = ['viewer', 'repository', 'node', '__type', '__schema'];
const USER_TYPE_FIELDS = ['login', 'id', 'name', 'email'];
const SEARCH_ENUM = ['ISSUE', 'PULL_REQUEST', 'REPOSITORY', 'USER', 'DISCUSSION', 'COMMIT'];

function gqlIssueState(issue: Issue): string {
  return issue.state === 'open' ? 'OPEN' : 'CLOSED';
}
function gqlPrState(pr: Pull): string {
  if (pr.merged) return 'MERGED';
  return pr.state === 'open' ? 'OPEN' : 'CLOSED';
}

interface GqlCtx {
  repoById: (dbid: number) => Repo | undefined;
  errors: Array<{ message: string }>;
}

function resolveIssueFields(repo: Repo, issue: Issue, fields: GqlField[], gctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (!ISSUE_TYPE_FIELDS.includes(f.name)) {
      gctx.errors.push({ message: `Cannot query field "${f.name}" on type "Issue".` });
      continue;
    }
    switch (f.name) {
      case 'id': out[key] = globalId('Issue', repo.id, issue.number); break;
      case 'number': out[key] = issue.number; break;
      case 'title': out[key] = issue.title; break;
      case 'state': out[key] = gqlIssueState(issue); break;
      case 'body': out[key] = issue.body; break;
      case 'url': out[key] = `https://github.com/${repo.owner}/${repo.name}/issues/${issue.number}`; break;
      case 'createdAt': out[key] = isoOf(issue.createdSeq); break;
      case 'updatedAt': out[key] = isoOf(issue.createdSeq); break;
      case 'author': out[key] = resolveUserFields(f.children, gctx); break;
      case 'labels': out[key] = { nodes: issue.labels.map((l) => ({ name: l.name })), totalCount: issue.labels.length }; break;
      case 'comments': out[key] = { nodes: issue.comments.map((c) => ({ id: globalId('IssueComment', repo.id, issue.number, c.id), body: c.body })), totalCount: issue.comments.length }; break;
      default: out[key] = null;
    }
  }
  return out;
}

function resolveUserFields(fields: GqlField[], gctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (!USER_TYPE_FIELDS.includes(f.name)) {
      gctx.errors.push({ message: `Cannot query field "${f.name}" on type "User".` });
      continue;
    }
    switch (f.name) {
      case 'login': out[key] = VIEWER_LOGIN; break;
      case 'id': out[key] = globalId('User', VIEWER_ID); break;
      case 'name': out[key] = VIEWER_NAME; break;
      case 'email': out[key] = VIEWER_EMAIL; break;
      default: out[key] = null;
    }
  }
  return out;
}

function resolvePrFields(repo: Repo, pr: Pull, fields: GqlField[], gctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (!PR_TYPE_FIELDS.includes(f.name)) {
      gctx.errors.push({ message: `Cannot query field "${f.name}" on type "PullRequest".` });
      continue;
    }
    switch (f.name) {
      case 'id': out[key] = globalId('PullRequest', repo.id, pr.number); break;
      case 'number': out[key] = pr.number; break;
      case 'title': out[key] = pr.title; break;
      case 'body': out[key] = pr.body; break;
      case 'state': out[key] = gqlPrState(pr); break;
      case 'merged': out[key] = pr.merged; break;
      case 'mergeable': out[key] = pr.state === 'open' ? (computeMergeable(repo, pr) ? 'MERGEABLE' : 'CONFLICTING') : 'UNKNOWN'; break;
      case 'headRefName': out[key] = pr.head; break;
      case 'baseRefName': out[key] = pr.base; break;
      case 'headRef': out[key] = { name: pr.head }; break;
      case 'baseRef': out[key] = { name: pr.base }; break;
      case 'url': out[key] = `https://github.com/${repo.owner}/${repo.name}/pull/${pr.number}`; break;
      case 'createdAt': out[key] = isoOf(pr.createdSeq); break;
      case 'mergedAt': out[key] = pr.mergedAt; break;
      case 'mergeCommit': out[key] = pr.mergeCommitSha ? { oid: pr.mergeCommitSha } : null; break;
      case 'author': out[key] = resolveUserFields(f.children, gctx); break;
      case 'files': {
        const baseTree = parseCommit(repo.objects.get(pr.baseSha)!.data).tree;
        const headTree = parseCommit(repo.objects.get(pr.headSha)!.data).tree;
        const files = diffFiles(repo, baseTree, headTree);
        const first = typeof f.args.first === 'number' ? f.args.first : files.length;
        out[key] = { nodes: files.slice(0, first).map((fl) => ({ path: fl.filename })), totalCount: files.length };
        break;
      }
      default: out[key] = null;
    }
  }
  return out;
}

// Resolve a Relay connection object: the requested subfields (nodes,
// edges, pageInfo, totalCount) are descended into — a node's fields are
// resolved against the node, never against the connection itself.
function resolveGqlConnection<T>(page: T[], total: number, pageInfo: Record<string, unknown>, fields: GqlField[], resolveNode: (item: T, children: GqlField[]) => Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (f.name === 'nodes') {
      out[key] = page.map((item) => resolveNode(item, f.children));
    } else if (f.name === 'edges') {
      const nodeChild = f.children.find((c) => c.name === 'node');
      out[key] = page.map((item) => ({ node: resolveNode(item, nodeChild ? nodeChild.children : []), cursor: null }));
    } else if (f.name === 'pageInfo') {
      const pi: Record<string, unknown> = {};
      for (const child of f.children) pi[child.alias ?? child.name] = pageInfo[child.name] ?? null;
      out[key] = pi;
    } else if (f.name === 'totalCount') {
      out[key] = total;
    } else {
      out[key] = null;
    }
  }
  return out;
}

function resolveRepoFields(repo: Repo, fields: GqlField[], gctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (!REPO_TYPE_FIELDS.includes(f.name)) {
      gctx.errors.push({ message: `Cannot query field "${f.name}" on type "Repository".` });
      continue;
    }
    switch (f.name) {
      case 'id': out[key] = globalId('Repository', repo.id); break;
      case 'databaseId': out[key] = repo.id; break;
      case 'name': out[key] = repo.name; break;
      case 'nameWithOwner': out[key] = `${repo.owner}/${repo.name}`; break;
      case 'owner': out[key] = resolveUserFields(f.children, gctx); break;
      case 'defaultBranchRef': {
        const tip = refTip(repo, repo.defaultBranch);
        out[key] = tip ? { name: repo.defaultBranch, target: { oid: tip } } : null;
        break;
      }
      case 'viewerPermission': out[key] = 'ADMIN'; break;
      case 'hasIssuesEnabled': out[key] = true; break;
      case 'description': out[key] = repo.description; break;
      case 'private': out[key] = repo.priv; break;
      case 'url': out[key] = `https://github.com/${repo.owner}/${repo.name}`; break;
      case 'createdAt': out[key] = isoOf(repo.createdSeq); break;
      case 'issue': {
        const num = f.args.number as number;
        const issue = repo.issues.find((i) => i.number === num);
        out[key] = issue ? resolveIssueFields(repo, issue, f.children, gctx) : null;
        break;
      }
      case 'issues': {
        let list = [...repo.issues];
        const states = f.args.states as string[] | undefined;
        if (states && states.length > 0) {
          const want = new Set(states.map((s) => String(s).toLowerCase()));
          list = list.filter((i) => want.has(i.state));
        }
        const orderBy = f.args.orderBy as Record<string, unknown> | undefined;
        const direction = orderBy && String(orderBy.direction ?? 'DESC').toUpperCase() === 'ASC' ? 1 : -1;
        list.sort((a, b) => (a.number - b.number) * direction);
        const first = typeof f.args.first === 'number' ? f.args.first : list.length;
        const after = typeof f.args.after === 'string' ? f.args.after : null;
        let startIdx = 0;
        if (after) {
          try {
            const decoded = b64decode(after).toString('utf8');
            const m = /^cursor:(\d+)$/.exec(decoded);
            if (m) {
              const idx = list.findIndex((i) => i.number === Number(m[1]));
              if (idx >= 0) startIdx = idx + 1;
            }
          } catch { /* ignore bad cursor */ }
        }
        const page = list.slice(startIdx, startIdx + first);
        const hasNext = startIdx + first < list.length;
        const endCursor = page.length > 0 ? b64encode(Buffer.from(`cursor:${page[page.length - 1]!.number}`, 'utf8')) : null;
        const startCursor = page.length > 0 ? b64encode(Buffer.from(`cursor:${page[0]!.number}`, 'utf8')) : null;
        out[key] = resolveGqlConnection(page, list.length, { hasNextPage: hasNext, hasPreviousPage: startIdx > 0, startCursor, endCursor }, f.children, (i, children) => resolveIssueFields(repo, i, children, gctx));
        break;
      }
      case 'pullRequests': {
        const first = typeof f.args.first === 'number' ? f.args.first : repo.pulls.length;
        const list = [...repo.pulls].sort((a, b) => a.number - b.number).slice(0, first);
        out[key] = resolveGqlConnection(list, repo.pulls.length, { hasNextPage: first < repo.pulls.length, hasPreviousPage: false, startCursor: null, endCursor: list.length > 0 ? b64encode(Buffer.from(`cursor:${list[list.length - 1]!.number}`, 'utf8')) : null }, f.children, (pr, children) => resolvePrFields(repo, pr, children, gctx));
        break;
      }
      case 'pullRequest': {
        const num = f.args.number as number;
        const pr = repo.pulls.find((p) => p.number === num);
        out[key] = pr ? resolvePrFields(repo, pr, f.children, gctx) : null;
        break;
      }
      default: out[key] = null;
    }
  }
  return out;
}

function typeIntrospection(name: string): Record<string, unknown> | null {
  const table: Record<string, { fields: string[]; enumValues: string[] }> = {
    Issue: { fields: ISSUE_TYPE_FIELDS, enumValues: [] },
    PullRequest: { fields: PR_TYPE_FIELDS, enumValues: [] },
    Repository: { fields: REPO_TYPE_FIELDS, enumValues: [] },
    User: { fields: USER_TYPE_FIELDS, enumValues: [] },
    SearchType: { fields: [], enumValues: SEARCH_ENUM },
    IssueState: { fields: [], enumValues: ['OPEN', 'CLOSED'] },
    PullRequestState: { fields: [], enumValues: ['OPEN', 'CLOSED', 'MERGED'] },
    MergeableState: { fields: [], enumValues: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
    OrderDirection: { fields: [], enumValues: ['ASC', 'DESC'] },
  };
  const t = table[name];
  if (!t) return null;
  return {
    name,
    kind: t.enumValues.length > 0 ? 'ENUM' : 'OBJECT',
    fields: t.fields.map((n) => ({ name: n, description: null, args: [], type: { name: 'String', kind: 'SCALAR' } })),
    enumValues: t.enumValues.map((n) => ({ name: n, description: null, isDeprecated: false, deprecationReason: null })),
  };
}

function resolveTypeField(f: GqlField, gctx: GqlCtx): Record<string, unknown> | null {
  const name = f.args.name as string;
  const full = typeIntrospection(name);
  if (!full) return null;
  const out: Record<string, unknown> = {};
  for (const child of f.children) {
    const key = child.alias ?? child.name;
    if (child.name === 'fields') out[key] = full.fields;
    else if (child.name === 'enumValues') out[key] = full.enumValues;
    else if (child.name === 'name') out[key] = full.name;
    else if (child.name === 'kind') out[key] = full.kind;
    else out[key] = null;
  }
  return out;
}

function executeOperation(doc: GqlDoc, variables: Record<string, unknown>): { data: Record<string, unknown> | null; errors: Array<{ message: string }> } {
  const gctx: GqlCtx = {
    repoById: (dbid) => {
      for (const r of repos.values()) if (r.id === dbid) return r;
      return undefined;
    },
    errors: [],
  };
  const data: Record<string, unknown> = {};
  if (doc.kind === 'mutation') {
    for (const f of doc.fields) {
      const key = f.alias ?? f.name;
      if (f.name === 'createIssue') {
        const input = f.args.input as Record<string, unknown>;
        const parsed = typeof input?.repositoryId === 'string' ? parseGlobalId(input.repositoryId) : null;
        const repo = parsed && parsed.kind === 'Repository' ? gctx.repoById(Number(parsed.parts[0])) : undefined;
        if (!repo) { data[key] = null; gctx.errors.push({ message: 'Could not resolve to a Repository with the global id.' }); continue; }
        const issue: Issue = {
          id: nextGlobalId++, number: repo.nextIssue++,
          title: typeof input?.title === 'string' ? input.title : '',
          body: typeof input?.body === 'string' ? input.body : '',
          state: 'open', labels: [], user: VIEWER_LOGIN, createdSeq: ++seq, comments: [],
          jsonCache: null,
        };
        repo.issues.push(issue);
        const inner: Record<string, unknown> = {};
        for (const child of f.children) {
          if (child.name === 'issue') inner[child.alias ?? 'issue'] = resolveIssueFields(repo, issue, child.children, gctx);
        }
        data[key] = inner;
      } else if (f.name === 'closeIssue') {
        const input = f.args.input as Record<string, unknown>;
        const parsed = typeof input?.issueId === 'string' ? parseGlobalId(input.issueId) : null;
        let found: { repo: Repo; issue: Issue } | null = null;
        if (parsed && parsed.kind === 'Issue') {
          const repo = gctx.repoById(Number(parsed.parts[0]));
          const issue = repo?.issues.find((i) => i.number === Number(parsed.parts[1]));
          if (repo && issue) found = { repo, issue };
        }
        if (!found) { data[key] = null; gctx.errors.push({ message: 'Could not resolve to an Issue with the global id.' }); continue; }
        found.issue.state = 'closed';
        invalidateIssue(found.issue);
        const inner: Record<string, unknown> = {};
        for (const child of f.children) {
          if (child.name === 'issue') inner[child.alias ?? 'issue'] = resolveIssueFields(found.repo, found.issue, child.children, gctx);
        }
        data[key] = inner;
      } else if (f.name === 'createPullRequest') {
        const input = f.args.input as Record<string, unknown>;
        const parsed = typeof input?.repositoryId === 'string' ? parseGlobalId(input.repositoryId) : null;
        const repo = parsed && parsed.kind === 'Repository' ? gctx.repoById(Number(parsed.parts[0])) : undefined;
        const head = typeof input?.headRefName === 'string' ? input.headRefName : '';
        const base = typeof input?.baseRefName === 'string' ? input.baseRefName : '';
        const headSha = repo ? refTip(repo, head) : undefined;
        const baseSha = repo ? refTip(repo, base) : undefined;
        if (!repo || !headSha || !baseSha) { data[key] = null; gctx.errors.push({ message: 'Could not resolve to a Repository or head branch.' }); continue; }
        const pr: Pull = {
          id: nextGlobalId++, number: repo.nextPull++,
          title: typeof input?.title === 'string' ? input.title : '',
          body: typeof input?.body === 'string' ? input.body : '',
          state: 'open', head, base, headSha, baseSha, merged: false, mergedAt: null, mergeCommitSha: null, createdSeq: ++seq,
        };
        repo.pulls.push(pr);
        const inner: Record<string, unknown> = {};
        for (const child of f.children) {
          if (child.name === 'pullRequest') inner[child.alias ?? 'pullRequest'] = resolvePrFields(repo, pr, child.children, gctx);
        }
        data[key] = inner;
      } else if (f.name === 'mergePullRequest') {
        const input = f.args.input as Record<string, unknown>;
        const parsed = typeof input?.pullRequestId === 'string' ? parseGlobalId(input.pullRequestId) : null;
        let found: { repo: Repo; pr: Pull } | null = null;
        if (parsed && parsed.kind === 'PullRequest') {
          const repo = gctx.repoById(Number(parsed.parts[0]));
          const pr = repo?.pulls.find((p) => p.number === Number(parsed.parts[1]));
          if (repo && pr) found = { repo, pr };
        }
        if (!found) { data[key] = null; gctx.errors.push({ message: 'Could not resolve to a PullRequest with the global id.' }); continue; }
        if (found.pr.state === 'open') {
          const result = squashMerge(found.repo, found.pr);
          if (result.conflict) { data[key] = null; gctx.errors.push({ message: 'Merge conflict.' }); continue; }
        }
        const inner: Record<string, unknown> = {};
        for (const child of f.children) {
          if (child.name === 'pullRequest') inner[child.alias ?? 'pullRequest'] = resolvePrFields(found.repo, found.pr, child.children, gctx);
        }
        data[key] = inner;
      } else if (f.name === 'addComment') {
        const input = f.args.input as Record<string, unknown>;
        const parsed = typeof input?.subjectId === 'string' ? parseGlobalId(input.subjectId) : null;
        let found: { repo: Repo; issue: Issue } | null = null;
        if (parsed && parsed.kind === 'Issue') {
          const repo = gctx.repoById(Number(parsed.parts[0]));
          const issue = repo?.issues.find((i) => i.number === Number(parsed.parts[1]));
          if (repo && issue) found = { repo, issue };
        }
        if (!found) { data[key] = null; gctx.errors.push({ message: 'Could not resolve to an Issue with the global id.' }); continue; }
        const comment: Comment = { id: found.repo.nextComment++, body: typeof input?.body === 'string' ? input.body : '', user: VIEWER_LOGIN, createdSeq: ++seq };
        found.issue.comments.push(comment);
        invalidateIssue(found.issue);
        const inner: Record<string, unknown> = {};
        for (const child of f.children) {
          if (child.name === 'commentEdge') {
            const node: Record<string, unknown> = {};
            for (const gc of child.children) {
              if (gc.name === 'node') {
                const n: Record<string, unknown> = {};
                for (const nc of gc.children) {
                  if (nc.name === 'id') n[nc.alias ?? 'id'] = globalId('IssueComment', found.repo.id, found.issue.number, comment.id);
                  else if (nc.name === 'body') n[nc.alias ?? 'body'] = comment.body;
                  else n[nc.alias ?? nc.name] = null;
                }
                node[gc.alias ?? 'node'] = n;
              }
            }
            inner[child.alias ?? 'commentEdge'] = node;
          }
        }
        data[key] = inner;
      } else {
        gctx.errors.push({ message: `Cannot query field "${f.name}" on type "Mutation".` });
        data[key] = null;
      }
    }
    return { data, errors: gctx.errors };
  }
  // query
  for (const f of doc.fields) {
    const key = f.alias ?? f.name;
    if (!QUERY_TYPE_FIELDS.includes(f.name)) {
      gctx.errors.push({ message: `Cannot query field "${f.name}" on type "Query".` });
      data[key] = null;
      continue;
    }
    if (f.name === 'viewer') {
      data[key] = resolveUserFields(f.children, gctx);
    } else if (f.name === 'repository') {
      const owner = f.args.owner as string;
      const name = f.args.name as string;
      if (owner !== VIEWER_LOGIN) { data[key] = null; continue; }
      const repo = getRepo(owner, name);
      data[key] = repo ? resolveRepoFields(repo, f.children, gctx) : null;
    } else if (f.name === 'node') {
      const parsed = typeof f.args.id === 'string' ? parseGlobalId(f.args.id) : null;
      let node: Record<string, unknown> | null = null;
      if (parsed && parsed.kind === 'Repository') {
        const repo = gctx.repoById(Number(parsed.parts[0]));
        if (repo) {
          node = { id: globalId('Repository', repo.id) };
          for (const child of f.children) {
            if (child.name === '...' && child.fragmentType === 'Repository') {
              Object.assign(node, resolveRepoFields(repo, child.children, gctx));
            } else if (child.name === 'id') {
              node[child.alias ?? 'id'] = globalId('Repository', repo.id);
            }
          }
        }
      }
      data[key] = node;
    } else if (f.name === '__type') {
      data[key] = resolveTypeField(f, gctx);
    } else if (f.name === '__schema') {
      data[key] = { queryType: { name: 'Query' }, mutationType: { name: 'Mutation' }, types: [] };
    }
  }
  return { data, errors: gctx.errors };
}

async function handleGraphQL(ctx: Ctx): Promise<boolean> {
  if (ctx.path !== '/api/graphql') return false;
  if (ctx.method !== 'POST') { errJson(ctx.res, 405, 'Method Not Allowed'); return true; }
  if (!needAuth(ctx)) return true;
  const body = await readJsonBody(ctx);
  if (!body.ok) { errJson(ctx.res, 400, 'Problems parsing JSON'); return true; }
  const runOne = (op: unknown): Record<string, unknown> => {
    if (!isRecord(op) || typeof op.query !== 'string') {
      return { data: null, errors: [{ message: 'Request must include a query string.' }] };
    }
    const variables = isRecord(op.variables) ? op.variables : {};
    try {
      const doc = new GqlParser(op.query, variables).parseDocument();
      const { data, errors } = executeOperation(doc, variables);
      const out: Record<string, unknown> = { data };
      if (errors.length > 0) out.errors = errors;
      return out;
    } catch (e) {
      return { data: null, errors: [{ message: e instanceof Error ? e.message : String(e) }] };
    }
  };
  if (Array.isArray(body.value)) {
    sendJson(ctx.res, 200, body.value.map(runOne));
  } else {
    sendJson(ctx.res, 200, runOne(body.value));
  }
  return true;
}

// ---------------------------------------------------------------------------
// MCP

interface McpToolDef {
  name: string;
  description: string;
  properties: Record<string, { type: string; description: string }>;
  required: string[];
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    properties: {
      name: { type: 'string', description: 'The name of the repository.' },
      description: { type: 'string', description: 'A short description of the repository.' },
      private: { type: 'boolean', description: 'Whether the repository is private.' },
    },
    required: ['name'],
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    properties: {
      owner: { type: 'string', description: 'The owner of the repository.' },
      repo: { type: 'string', description: 'The name of the repository.' },
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    properties: {
      owner: { type: 'string', description: 'The owner of the repository.' },
      repo: { type: 'string', description: 'The name of the repository.' },
      title: { type: 'string', description: 'The title of the issue.' },
      body: { type: 'string', description: 'The body of the issue.' },
    },
    required: ['owner', 'repo', 'title'],
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository, optionally filtered by state.',
    properties: {
      owner: { type: 'string', description: 'The owner of the repository.' },
      repo: { type: 'string', description: 'The name of the repository.' },
      state: { type: 'string', description: 'Issue state: open, closed, or all.' },
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'get_issue',
    description: 'Get a single issue by number.',
    properties: {
      owner: { type: 'string', description: 'The owner of the repository.' },
      repo: { type: 'string', description: 'The name of the repository.' },
      issue_number: { type: 'integer', description: 'The issue number.' },
    },
    required: ['owner', 'repo', 'issue_number'],
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    properties: {
      owner: { type: 'string', description: 'The owner of the repository.' },
      repo: { type: 'string', description: 'The name of the repository.' },
      title: { type: 'string', description: 'The title of the pull request.' },
      body: { type: 'string', description: 'The body of the pull request.' },
      head: { type: 'string', description: 'The head branch name.' },
      base: { type: 'string', description: 'The base branch name.' },
    },
    required: ['owner', 'repo', 'title', 'head', 'base'],
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request with a squash commit.',
    properties: {
      owner: { type: 'string', description: 'The owner of the repository.' },
      repo: { type: 'string', description: 'The name of the repository.' },
      pull_number: { type: 'integer', description: 'The pull request number.' },
    },
    required: ['owner', 'repo', 'pull_number'],
  },
  {
    name: 'list_pull_requests',
    description: 'List pull requests in a repository, optionally filtered by state.',
    properties: {
      owner: { type: 'string', description: 'The owner of the repository.' },
      repo: { type: 'string', description: 'The name of the repository.' },
      state: { type: 'string', description: 'Pull request state: open, closed, or all.' },
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'list_repos',
    description: 'List repositories owned by the authenticated user.',
    properties: {},
    required: [],
  },
  {
    name: 'create_label',
    description: 'Create a label in a repository.',
    properties: {
      owner: { type: 'string', description: 'The owner of the repository.' },
      repo: { type: 'string', description: 'The name of the repository.' },
      name: { type: 'string', description: 'The label name.' },
      color: { type: 'string', description: 'The label color (hex, without #).' },
    },
    required: ['owner', 'repo', 'name'],
  },
];

const MCP_TOOLS_JSON = JSON.stringify(MCP_TOOLS.map((t) => ({
  name: t.name,
  description: t.description,
  inputSchema: { type: 'object', properties: t.properties, required: t.required },
})));

function mcpToolResult(obj: unknown, isError = false): Record<string, unknown> {
  const text = typeof obj === 'string' ? obj : JSON.stringify(obj);
  return {
    content: [{ type: 'text', text }],
    structuredContent: isRecord(obj) || Array.isArray(obj) ? obj : undefined,
    isError,
  };
}

function mcpFindTool(name: string): McpToolDef | undefined {
  const norm = name.toLowerCase().replace(/[^a-z0-9]/g, '');
  return MCP_TOOLS.find((t) => {
    const tn = t.name.replace(/[^a-z0-9]/g, '');
    return norm === tn || norm.endsWith(tn);
  });
}

function mcpCallTool(name: string, args: Record<string, unknown>): { result?: Record<string, unknown>; error?: { code: number; message: string } } {
  const tool = mcpFindTool(name);
  if (!tool) return { error: { code: -32602, message: `Unknown tool: ${name}` } };
  for (const req of tool.required) {
    if (args[req] === undefined || args[req] === null || args[req] === '') {
      return { result: mcpToolResult(`Missing required argument: ${req}`, true) };
    }
  }
  const ownerOf = (): string => {
    const full = typeof args.full_name === 'string' ? args.full_name : '';
    if (full.includes('/')) return full.split('/')[0]!;
    return typeof args.owner === 'string' ? args.owner : VIEWER_LOGIN;
  };
  const repoOf = (): string => {
    const full = typeof args.full_name === 'string' ? args.full_name : '';
    if (full.includes('/')) return full.split('/')[1]!;
    return typeof args.repo === 'string' ? args.repo : typeof args.repository === 'string' ? args.repository : '';
  };
  const lookupRepo = (): Repo | undefined => getRepo(ownerOf(), repoOf());
  switch (tool.name) {
    case 'create_repo': {
      const rname = String(args.name ?? '');
      if (getRepo(VIEWER_LOGIN, rname)) return { result: mcpToolResult(`Repository ${VIEWER_LOGIN}/${rname} already exists`, true) };
      const repo = createRepoRecord(rname, typeof args.description === 'string' ? args.description : '', args.private === true);
      return { result: mcpToolResult(repoJson(repo)) };
    }
    case 'get_repo': {
      const repo = lookupRepo();
      if (!repo) return { result: mcpToolResult(`Repository ${ownerOf()}/${repoOf()} not found`, true) };
      return { result: mcpToolResult(repoJson(repo)) };
    }
    case 'create_issue': {
      const repo = lookupRepo();
      if (!repo) return { result: mcpToolResult(`Repository ${ownerOf()}/${repoOf()} not found`, true) };
      const issue: Issue = {
        id: nextGlobalId++, number: repo.nextIssue++,
        title: String(args.title ?? ''), body: typeof args.body === 'string' ? args.body : '',
        state: 'open', labels: [], user: VIEWER_LOGIN, createdSeq: ++seq, comments: [],
        jsonCache: null,
      };
      repo.issues.push(issue);
      return { result: mcpToolResult(issueJson(repo, issue)) };
    }
    case 'list_issues': {
      const repo = lookupRepo();
      if (!repo) return { result: mcpToolResult(`Repository ${ownerOf()}/${repoOf()} not found`, true) };
      const state = typeof args.state === 'string' ? args.state : 'open';
      const list = repo.issues.filter((i) => state === 'all' || i.state === state).map((i) => issueJson(repo, i));
      return { result: mcpToolResult({ issues: list }) };
    }
    case 'get_issue': {
      const repo = lookupRepo();
      const num = Number(args.issue_number ?? args.number ?? 0);
      const issue = repo?.issues.find((i) => i.number === num);
      if (!repo || !issue) return { result: mcpToolResult('Issue not found', true) };
      return { result: mcpToolResult(issueJson(repo, issue)) };
    }
    case 'create_pull_request': {
      const repo = lookupRepo();
      if (!repo) return { result: mcpToolResult(`Repository ${ownerOf()}/${repoOf()} not found`, true) };
      const head = String(args.head ?? '');
      const base = String(args.base ?? '');
      const headSha = refTip(repo, head);
      const baseSha = refTip(repo, base);
      if (!headSha || !baseSha) return { result: mcpToolResult('head or base branch does not exist', true) };
      const pr: Pull = {
        id: nextGlobalId++, number: repo.nextPull++,
        title: String(args.title ?? ''), body: typeof args.body === 'string' ? args.body : '',
        state: 'open', head, base, headSha, baseSha, merged: false, mergedAt: null, mergeCommitSha: null, createdSeq: ++seq,
      };
      repo.pulls.push(pr);
      return { result: mcpToolResult(pullJson(repo, pr)) };
    }
    case 'merge_pull_request': {
      const repo = lookupRepo();
      const num = Number(args.pull_number ?? args.number ?? 0);
      const pr = repo?.pulls.find((p) => p.number === num);
      if (!repo || !pr) return { result: mcpToolResult('Pull request not found', true) };
      if (pr.state !== 'open') return { result: mcpToolResult('Pull request is already closed', true) };
      const result = squashMerge(repo, pr);
      if (result.conflict) return { result: mcpToolResult('Merge conflict', true) };
      if (!result.ok) return { result: mcpToolResult('Merge failed', true) };
      return { result: mcpToolResult({ sha: result.sha, merged: true, message: `Pull request #${num} successfully merged`, number: num }) };
    }
    case 'list_pull_requests': {
      const repo = lookupRepo();
      if (!repo) return { result: mcpToolResult(`Repository ${ownerOf()}/${repoOf()} not found`, true) };
      const state = typeof args.state === 'string' ? args.state : 'open';
      const list = repo.pulls.filter((pr) => state === 'all' || pr.state === state).map((pr) => pullJson(repo, pr));
      return { result: mcpToolResult({ pull_requests: list }) };
    }
    case 'list_repos': {
      return { result: mcpToolResult({ repositories: viewerRepos().map(repoJson) }) };
    }
    case 'create_label': {
      const repo = lookupRepo();
      if (!repo) return { result: mcpToolResult(`Repository ${ownerOf()}/${repoOf()} not found`, true) };
      const label: Label = { name: String(args.name ?? ''), color: typeof args.color === 'string' ? args.color : 'ededed' };
      repo.labels.set(label.name, label);
      return { result: mcpToolResult({ name: label.name, color: label.color }) };
    }
    default:
      return { error: { code: -32602, message: `Unknown tool: ${name}` } };
  }
}

async function handleMcp(ctx: Ctx): Promise<boolean> {
  if (ctx.path !== '/mcp') return false;
  if (ctx.method === 'DELETE') {
    ctx.res.writeHead(200, { 'x-github-request-id': `req-${++reqCounter}` });
    ctx.res.end();
    return true;
  }
  if (ctx.method !== 'POST') { errJson(ctx.res, 405, 'Method Not Allowed'); return true; }
  if (!needAuth(ctx)) return true;
  const raw = await readBody(ctx.req).catch(() => Buffer.alloc(0));
  const text = raw.toString('utf8');
  let parsed: unknown;
  try {
    parsed = JSON.parse(text);
  } catch {
    const idMatch = /"id"\s*:\s*("[^"]*"|\d+)/.exec(text);
    const id = idMatch ? JSON.parse(idMatch[1]!) : null;
    sendJson(ctx.res, 400, { jsonrpc: '2.0', id, error: { code: -32700, message: 'Parse error' } });
    return true;
  }
  const handleOne = (msg: unknown): Record<string, unknown> | null => {
    if (!isRecord(msg) || typeof msg.method !== 'string') {
      return { jsonrpc: '2.0', id: isRecord(msg) ? (msg.id ?? null) : null, error: { code: -32600, message: 'Invalid Request' } };
    }
    const id = msg.id ?? null;
    const method = msg.method;
    const params = isRecord(msg.params) ? msg.params : {};
    if (method === 'server/discover') {
      return {
        jsonrpc: '2.0', id,
        result: {
          supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'],
          capabilities: { tools: {} },
          serverInfo: { name: 'github-forge', version: '1.0.0' },
          _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'github-forge', version: '1.0.0' } },
        },
      };
    }
    if (method === 'initialize') {
      const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25';
      const accepted = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];
      const negotiated = accepted.includes(requested) ? requested : '2025-11-25';
      return {
        jsonrpc: '2.0', id,
        result: {
          protocolVersion: negotiated,
          capabilities: { tools: {} },
          serverInfo: { name: 'github-forge', version: '1.0.0' },
        },
      };
    }
    if (method === 'notifications/initialized' || method.startsWith('notifications/')) {
      return null; // notification: no JSON-RPC response
    }
    if (method === 'tools/list') {
      return { jsonrpc: '2.0', id, result: { tools: JSON.parse(MCP_TOOLS_JSON) } };
    }
    if (method === 'tools/call') {
      const name = typeof params.name === 'string' ? params.name : '';
      const args = isRecord(params.arguments) ? params.arguments : {};
      const outcome = mcpCallTool(name, args);
      if (outcome.error) {
        return { jsonrpc: '2.0', id, error: outcome.error };
      }
      return { jsonrpc: '2.0', id, result: outcome.result };
    }
    if (method === 'ping') {
      return { jsonrpc: '2.0', id, result: {} };
    }
    return { jsonrpc: '2.0', id, error: { code: -32601, message: `Method not found: ${method}` } };
  };
  if (Array.isArray(parsed)) {
    const results = parsed.map(handleOne).filter((r) => r !== null);
    sendJson(ctx.res, 200, results);
    return true;
  }
  const result = handleOne(parsed);
  if (result === null) {
    ctx.res.writeHead(202, { 'x-github-request-id': `req-${++reqCounter}` });
    ctx.res.end();
    return true;
  }
  sendJson(ctx.res, 200, result);
  return true;
}

// ---------------------------------------------------------------------------
// server

// Fast path for the read workload: GET /api/v3/repos/{owner}/{repo}/issues/{n}
// with no query string. Serves the issue's cached JSON without URL parsing,
// the git/GraphQL/MCP dispatch or the generic REST router. Anything that does
// not match exactly (other owners, missing repo/issue, empty cache, no auth)
// returns false and the request falls through to the normal handlers.
function tryFastIssueGet(req: IncomingMessage, res: ServerResponse): boolean {
  if (req.method !== 'GET') return false;
  const url = req.url ?? '';
  if (url.includes('?')) return false;
  const m = /^\/api\/v3\/repos\/([^/]+)\/([^/]+)\/issues\/(\d+)$/.exec(url);
  if (!m) return false;
  let owner = m[1]!;
  let name = m[2]!;
  try { owner = decodeURIComponent(owner); name = decodeURIComponent(name); } catch { return false; }
  if (owner !== VIEWER_LOGIN) return false;
  if (TOKEN !== '') {
    const h = req.headers.authorization ?? '';
    if (!h.startsWith('Bearer ')) return false;
    const tok = h.slice(7);
    if (tok.length !== TOKEN.length) return false;
    try {
      if (!timingSafeEqual(Buffer.from(tok), Buffer.from(TOKEN))) return false;
    } catch { return false; }
  }
  const repo = getRepo(owner, name);
  if (!repo) return false;
  const issue = repo.issues.find((i) => i.number === Number(m[3]));
  if (!issue || !issue.jsonCache) return false;
  const body = issue.jsonCache;
  res.writeHead(200, {
    'content-type': JSON_TYPE,
    'content-length': String(body.length),
    'x-github-request-id': `req-${++reqCounter}`,
  });
  res.end(body);
  return true;
}

export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    if (tryFastIssueGet(req, res)) return;
    void (async (): Promise<void> => {
      try {
        const url = new URL(req.url ?? '/', 'http://entry');
        const ctx: Ctx = {
          req, res,
          method: req.method ?? 'GET',
          path: url.pathname,
          query: url.searchParams,
          host: req.headers.host ?? '127.0.0.1',
        };
        if (ctx.method === 'GET' && ctx.path === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }
        if (await handleGit(ctx)) return;
        if (await handleGraphQL(ctx)) return;
        if (await handleMcp(ctx)) return;
        if (await handleRest(ctx)) return;
        errJson(res, 404, 'Not Found');
      } catch (e) {
        try { errJson(res, 500, e instanceof Error ? e.message : String(e)); } catch { /* socket gone */ }
      }
    })();
  });
}
