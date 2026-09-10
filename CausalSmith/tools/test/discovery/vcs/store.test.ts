import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { blobId, contentKey, type NodeBlob } from "../../../src/discovery/vcs/node.js";
import { VcsStore, commitId } from "../../../src/discovery/vcs/store.js";

// The object store is the floor everything else stands on: idempotent immutable
// objects, verified reads, compare-and-swap ref moves. Each property here is one
// the old stores lacked and paid for (w3: a round overwrote the previous round's
// only copy; torn writes on NFS; two writers each believing they advanced).

const stmt = (statement: string): NodeBlob => ({
  node_type: "statement",
  body: { id: "thm:main", kind: "theorem", statement, depends_on: [], free_symbols: [] },
});

describe("vcs store", () => {
  let dir: string;
  let store: VcsStore;
  beforeEach(async () => {
    dir = await mkdtemp(path.join(os.tmpdir(), "vcs-store-"));
    store = new VcsStore(dir);
    await store.init();
  });
  afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

  it("content-addresses blobs independent of key order and verifies them on read", async () => {
    const a = stmt("x");
    const b: NodeBlob = { body: { free_symbols: [], depends_on: [], statement: "x", kind: "theorem", id: "thm:main" }, node_type: "statement" };
    expect(blobId(a)).toBe(blobId(b));
    const id = await store.writeBlob(a);
    expect(await store.writeBlob(b)).toBe(id);
    expect(await store.readBlob(id)).toEqual(a);
  });

  it("refuses a blob whose bytes no longer hash to its name", async () => {
    const id = await store.writeBlob(stmt("x"));
    const file = path.join(dir, "objects", `${id}.json`);
    const tampered = JSON.parse(await readFile(file, "utf8")) as NodeBlob & { body: { statement: string } };
    tampered.body.statement = "y";
    await writeFile(file, JSON.stringify(tampered), "utf8");
    await expect(store.readBlob(id)).rejects.toThrow(/corrupt/);
  });

  it("refuses a commit naming a missing object or parent", async () => {
    const missing = "0".repeat(64);
    await expect(store.writeCommit({
      parents: [], tree: { "thm:main": { blob: missing, pos: 0 } }, author: "t", kind: "initial", message: "m", time: "now",
    })).rejects.toThrow(/missing object/);
    const id = await store.writeBlob(stmt("x"));
    await expect(store.writeCommit({
      parents: [missing], tree: { "thm:main": { blob: id, pos: 0 } }, author: "t", kind: "direct", message: "m", time: "now",
    })).rejects.toThrow(/parent commit/);
  });

  it("moves main only by compare-and-swap and journals every move", async () => {
    const blob = await store.writeBlob(stmt("x"));
    const c1 = await store.writeCommit({ parents: [], tree: { "thm:main": { blob, pos: 0 } }, author: "t", kind: "initial", message: "one", time: "t1" });
    const c2 = await store.writeCommit({ parents: [c1], tree: { "thm:main": { blob, pos: 1 } }, author: "t", kind: "direct", message: "two", time: "t2" });
    expect(c1).not.toBe(c2);
    await store.updateRef("main", c1, null, "init");
    await expect(store.updateRef("main", c2, null, "stale expectation")).rejects.toThrow(/moved under us/);
    await store.updateRef("main", c2, c1, "advance");
    expect(await store.readRef("main")).toBe(c2);
    const log = await store.readReflog();
    expect(log.map((e) => [e.from, e.to])).toEqual([[null, c1], [c1, c2]]);
    expect((await store.history(c2)).map((c) => c.message)).toEqual(["two", "one"]);
  });

  it("resolves main, full ids and unambiguous prefixes", async () => {
    const blob = await store.writeBlob(stmt("x"));
    const c1 = await store.writeCommit({ parents: [], tree: { "thm:main": { blob, pos: 0 } }, author: "t", kind: "initial", message: "one", time: "t1" });
    await store.updateRef("main", c1, null, "init");
    expect(await store.resolve("main")).toBe(c1);
    expect(await store.resolve(c1.slice(0, 10))).toBe(c1);
    await expect(store.resolve("f".repeat(64))).rejects.toThrow(/unknown commit/);
    await expect(store.resolve("nope")).rejects.toThrow(/neither/);
  });

  it("commit ids are a pure function of the body", () => {
    const body = { parents: [], tree: {}, author: "t", kind: "initial" as const, message: "m", time: "t" };
    expect(commitId(body)).toBe(commitId({ ...body }));
    expect(commitId(body)).not.toBe(commitId({ ...body, message: "n" }));
  });

  it("content keys ignore TeX re-flow, prose, edges and proofs but not the claim", () => {
    const claim = "Let $x \\in \\mathbb{R}$. Then $x^2 \\ge 0$.";
    const base = stmt(claim);
    const reflowed = stmt("Let $x \\in\n  \\mathbb{R}$. Then $x^2\\ge 0$.");
    const withProof = stmt(claim);
    if (withProof.node_type === "statement") Object.assign(withProof.body, { proof_tex: "trivial", depends_on: ["ass:a"], justification: "why" });
    const changed = stmt("Let $x \\in \\mathbb{R}$. Then $x^2 > 0$.");
    expect(contentKey(reflowed)).toBe(contentKey(base));
    expect(contentKey(withProof)).toBe(contentKey(base));
    expect(contentKey(changed)).not.toBe(contentKey(base));
    expect(blobId(reflowed)).not.toBe(blobId(base)); // storage identity still sees the bytes
  });
});
