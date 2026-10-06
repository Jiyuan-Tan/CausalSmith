// The versioned theorem graph: object store.
//
// Git's data model in plain JSON, one store per run under `discovery/vcs/`:
//   objects/<sha>.json   node blobs, content-addressed (see node.ts)
//   commits/<sha>.json   {parents, tree, author, kind, message, time}, content-addressed
//   refs/main            the current commit id (one line)
//   reflog.jsonl         every ref move, append-only
//
// Robustness rules, all of them local to this file:
//   • Objects are immutable and idempotent to write: a blob that already exists is
//     never rewritten, so no writer can corrupt what another commit points at.
//   • Every read re-hashes and refuses a blob whose bytes do not match its name.
//   • The ref moves by compare-and-swap under a lock directory, so two writers can
//     never both believe they advanced main from the same parent.
//   • Writes go through atomic temp+rename; a crash leaves unreferenced objects at
//     worst, never a half-written commit or a torn ref.
import { existsSync } from "node:fs";
import { appendFile, mkdir, readFile, readdir, rename, rm, rmdir, writeFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { writeTextAtomic } from "../../shared/json_atomic.js";
import { stableJson } from "../../shared/stable_json.js";
import { artifactPath } from "../../paths.js";
import type { PipelineContext } from "../../types.js";
import { blobId, isNodeBlob, sha256Hex, type NodeBlob, type NodeId } from "./node.js";

export interface TreeEntry {
  /** The node's blob id. */
  blob: string;
  /** Layout order within its section of the rendered paper. Not content: two
   *  commits may disagree on it without conflict. */
  pos: number;
}
export type Tree = Record<NodeId, TreeEntry>;

export type CommitKind = "initial" | "direct" | "pr" | "merge" | "reset";

export interface CommitBody {
  parents: string[];
  tree: Tree;
  /** `pipeline` | `orchestrator` | `solver:<unit>` | `adjudicator` | `converter`. */
  author: string;
  kind: CommitKind;
  message: string;
  time: string;
  /** Free-form provenance (round number, unit, base commit of a PR, …). */
  meta?: Record<string, unknown>;
}
export interface Commit extends CommitBody {
  id: string;
}

export interface ReflogEntry {
  time: string;
  ref: string;
  from: string | null;
  to: string;
  note: string;
  pid: number;
}

const SHA_RE = /^[a-f0-9]{64}$/;

export function assertSha(value: string, what: string): void {
  if (!SHA_RE.test(value)) throw new Error(`${what}: '${value}' is not an object id`);
}

export function commitId(body: CommitBody): string {
  return sha256Hex(stableJson(body));
}

export const MAIN_REF = "main";

export class VcsStore {
  constructor(readonly dir: string) {}

  static path(ctx: PipelineContext): string {
    return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "vcs");
  }
  static at(ctx: PipelineContext): VcsStore {
    return new VcsStore(VcsStore.path(ctx));
  }

  exists(): boolean {
    return existsSync(path.join(this.dir, "refs", MAIN_REF));
  }

  private objectPath(id: string): string {
    return path.join(this.dir, "objects", `${id}.json`);
  }
  private commitPath(id: string): string {
    return path.join(this.dir, "commits", `${id}.json`);
  }
  private refPath(ref: string): string {
    return path.join(this.dir, "refs", ref);
  }
  private get reflogPath(): string {
    return path.join(this.dir, "reflog.jsonl");
  }
  private get lockDir(): string {
    return path.join(this.dir, "refs", ".lock");
  }

  async init(): Promise<void> {
    await mkdir(path.join(this.dir, "objects"), { recursive: true });
    await mkdir(path.join(this.dir, "commits"), { recursive: true });
    await mkdir(path.join(this.dir, "refs"), { recursive: true });
  }

  // -- objects -------------------------------------------------------------------

  /** Write a blob; returns its id. Idempotent: an existing object is left untouched. */
  async writeBlob(blob: NodeBlob): Promise<string> {
    const id = blobId(blob);
    const target = this.objectPath(id);
    if (!existsSync(target)) await writeTextAtomic(target, JSON.stringify(blob, null, 2));
    return id;
  }

  hasBlob(id: string): boolean {
    return existsSync(this.objectPath(id));
  }

  /** Read and VERIFY a blob: the bytes must hash to the requested id. */
  async readBlob(id: string): Promise<NodeBlob> {
    assertSha(id, "blob id");
    let parsed: unknown;
    try {
      parsed = JSON.parse(await readFile(this.objectPath(id), "utf8"));
    } catch (err) {
      throw new Error(`vcs: object ${id} unreadable: ${err instanceof Error ? err.message : String(err)}`);
    }
    if (!isNodeBlob(parsed)) throw new Error(`vcs: object ${id} is not a node blob`);
    const actual = blobId(parsed);
    if (actual !== id) throw new Error(`vcs: object ${id} is corrupt (content hashes to ${actual})`);
    return parsed;
  }

  // -- commits -------------------------------------------------------------------

  async writeCommit(body: CommitBody): Promise<string> {
    for (const parent of body.parents) {
      assertSha(parent, "parent");
      if (!existsSync(this.commitPath(parent))) throw new Error(`vcs: parent commit ${parent} does not exist`);
    }
    for (const [nodeId, entry] of Object.entries(body.tree)) {
      assertSha(entry.blob, `tree entry ${nodeId}`);
      if (!this.hasBlob(entry.blob)) throw new Error(`vcs: tree entry ${nodeId} names a missing object ${entry.blob}`);
      if (!Number.isFinite(entry.pos)) throw new Error(`vcs: tree entry ${nodeId} has no layout position`);
    }
    const id = commitId(body);
    const target = this.commitPath(id);
    if (!existsSync(target)) await writeTextAtomic(target, JSON.stringify(body, null, 2));
    return id;
  }

  async readCommit(id: string): Promise<Commit> {
    assertSha(id, "commit id");
    let parsed: CommitBody;
    try {
      parsed = JSON.parse(await readFile(this.commitPath(id), "utf8")) as CommitBody;
    } catch (err) {
      throw new Error(`vcs: commit ${id} unreadable: ${err instanceof Error ? err.message : String(err)}`);
    }
    const actual = commitId(parsed);
    if (actual !== id) throw new Error(`vcs: commit ${id} is corrupt (content hashes to ${actual})`);
    return { ...parsed, id };
  }

  hasCommit(id: string): boolean {
    return SHA_RE.test(id) && existsSync(this.commitPath(id));
  }

  /** Resolve `main`, a full id, or an unambiguous id prefix (≥ 7 hex chars). */
  async resolve(spec: string): Promise<string> {
    if (spec === MAIN_REF || spec === "HEAD") {
      const head = await this.readRef(MAIN_REF);
      if (head === null) throw new Error("vcs: no main commit (store not initialized)");
      return head;
    }
    if (SHA_RE.test(spec)) {
      if (!this.hasCommit(spec)) throw new Error(`vcs: unknown commit ${spec}`);
      return spec;
    }
    if (!/^[a-f0-9]{7,63}$/.test(spec)) throw new Error(`vcs: '${spec}' is neither 'main' nor a commit id`);
    const matches = (await this.listCommitIds()).filter((id) => id.startsWith(spec));
    if (matches.length === 1) return matches[0];
    if (matches.length === 0) throw new Error(`vcs: no commit starts with ${spec}`);
    throw new Error(`vcs: ambiguous prefix ${spec} (${matches.length} commits)`);
  }

  async listCommitIds(): Promise<string[]> {
    const dir = path.join(this.dir, "commits");
    if (!existsSync(dir)) return [];
    return (await readdir(dir)).filter((n) => n.endsWith(".json")).map((n) => n.slice(0, -5)).filter((n) => SHA_RE.test(n));
  }

  async listObjectIds(): Promise<string[]> {
    const dir = path.join(this.dir, "objects");
    if (!existsSync(dir)) return [];
    return (await readdir(dir)).filter((n) => n.endsWith(".json")).map((n) => n.slice(0, -5)).filter((n) => SHA_RE.test(n));
  }

  /** First-parent history from `from` (newest first), at most `limit` entries. */
  async history(from: string, limit = Number.POSITIVE_INFINITY): Promise<Commit[]> {
    const out: Commit[] = [];
    let cursor: string | undefined = from;
    const seen = new Set<string>();
    while (cursor !== undefined && out.length < limit) {
      if (seen.has(cursor)) throw new Error(`vcs: history cycle at ${cursor}`);
      seen.add(cursor);
      const commit = await this.readCommit(cursor);
      out.push(commit);
      cursor = commit.parents[0];
    }
    return out;
  }

  // -- refs ----------------------------------------------------------------------

  async readRef(ref: string = MAIN_REF): Promise<string | null> {
    const p = this.refPath(ref);
    if (!existsSync(p)) return null;
    const value = (await readFile(p, "utf8")).trim();
    assertSha(value, `ref ${ref}`);
    return value;
  }

  /** Move a ref by compare-and-swap: refuses when the ref no longer holds
   *  `expected` (null = must not exist yet). Journals the move. */
  async updateRef(ref: string, to: string, expected: string | null, note: string): Promise<void> {
    assertSha(to, "ref target");
    if (!this.hasCommit(to)) throw new Error(`vcs: cannot point ${ref} at missing commit ${to}`);
    await this.withLock(async () => {
      const current = await this.readRef(ref);
      if (current !== expected) {
        throw new Error(
          `vcs: ${ref} moved under us (expected ${expected ?? "<none>"}, found ${current ?? "<none>"}); ` +
          "re-read main and rebuild the commit on it",
        );
      }
      await writeTextAtomic(this.refPath(ref), `${to}\n`);
      const entry: ReflogEntry = { time: new Date().toISOString(), ref, from: current, to, note, pid: process.pid };
      await appendFile(this.reflogPath, `${JSON.stringify(entry)}\n`, "utf8");
    });
  }

  async readReflog(): Promise<ReflogEntry[]> {
    if (!existsSync(this.reflogPath)) return [];
    return (await readFile(this.reflogPath, "utf8"))
      .split("\n")
      .filter((line) => line.trim().length > 0)
      .map((line) => JSON.parse(line) as ReflogEntry);
  }

  /** Serialize ref moves. `mkdir` is atomic on POSIX filesystems (NFS included);
   *  a lock older than `STALE_LOCK_MS` whose owner pid is gone is reclaimed. */
  private async withLock<T>(fn: () => Promise<T>): Promise<T> {
    const STALE_LOCK_MS = 10 * 60_000;
    const deadline = Date.now() + 30_000;
    // The lock is staged with its owner record and renamed into place, so a lock
    // directory without an owner file cannot be observed by a contender.
    const staged = `${this.lockDir}.staging-${process.pid}-${Date.now()}`;
    await mkdir(staged, { recursive: true });
    await writeFile(path.join(staged, "owner"), `${process.pid} ${new Date().toISOString()}\n`, "utf8");
    for (;;) {
      try {
        await rename(staged, this.lockDir);
        break;
      } catch (err) {
        const code = (err as NodeJS.ErrnoException).code;
        if (code !== "EEXIST" && code !== "ENOTEMPTY" && code !== "EPERM") { await rm(staged, { recursive: true, force: true }); throw err; }
        const ownerFile = path.join(this.lockDir, "owner");
        let stale = false;
        try {
          const [pidText, timeText] = (await readFile(ownerFile, "utf8")).trim().split(/\s+/);
          const age = Date.now() - Date.parse(timeText ?? "");
          stale = !pidAlive(Number(pidText)) && (Number.isNaN(age) || age > STALE_LOCK_MS);
        } catch {
          stale = !existsSync(this.lockDir);
        }
        if (stale) {
          await rm(this.lockDir, { recursive: true, force: true });
          continue;
        }
        if (Date.now() > deadline) { await rm(staged, { recursive: true, force: true }); throw new Error(`vcs: ref lock held by another writer (${this.lockDir})`); }
        await new Promise((r) => setTimeout(r, 200));
      }
    }
    try {
      return await fn();
    } finally {
      await rm(path.join(this.lockDir, "owner"), { force: true });
      await rmdir(this.lockDir).catch(() => {});
    }
  }
}

function pidAlive(pid: number): boolean {
  if (!Number.isFinite(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch (err) {
    return (err as NodeJS.ErrnoException).code === "EPERM";
  }
}
