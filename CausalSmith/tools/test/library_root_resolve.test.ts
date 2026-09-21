import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { loadLibraryLenient } from "../src/formalization/reuse_retrieval.js";
import { resolveLibraryRoot } from "../src/library/schema.js";

const dirs: string[] = [];
afterEach(async () => {
  for (const d of dirs.splice(0)) await rm(d, { recursive: true, force: true });
});

describe("library root resolution", () => {
  it("accepts the CausalSmith package dir and finds the index one level up", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "libroot-"));
    dirs.push(root);
    await mkdir(path.join(root, "doc"), { recursive: true });
    await mkdir(path.join(root, "CausalSmith"), { recursive: true });
    await writeFile(
      path.join(root, "doc", "library_index.json"),
      JSON.stringify({ commit: "x", toolchain: "y", modules: {}, entries: [{ name: "Foo.bar", kind: "theorem", statement: "True", file: "Causalean/Foo.lean", module: "Causalean.Foo", line: 1, docstring: "", usesSorry: false, axioms: [] }] }),
    );
    const pkg = path.join(root, "CausalSmith");
    expect(resolveLibraryRoot(pkg)).toBe(root);
    expect(resolveLibraryRoot(root)).toBe(root);
    expect(loadLibraryLenient(pkg)).not.toBeNull();
  });
  it("leaves an unrelated root alone", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "libroot-"));
    dirs.push(root);
    expect(resolveLibraryRoot(root)).toBe(root);
    expect(loadLibraryLenient(root)).toBeNull();
  });
});
