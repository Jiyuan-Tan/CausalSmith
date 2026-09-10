import { afterEach, expect, it } from "vitest";
import { mkdtemp, mkdir, writeFile, rm, symlink } from "node:fs/promises";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { join, resolve } from "node:path";
import { tmpdir } from "node:os";

const execute = promisify(execFile);
const dirs: string[] = [];
afterEach(async () => { await Promise.all(dirs.splice(0).map(dir => rm(dir, { recursive: true, force: true }))); });
const source = "private def helper : Nat := 1\n";
async function fixture() {
  const root = await mkdtemp(join(tmpdir(), "snippet-path-")); dirs.push(root);
  const cs = join(root, "CausalSmith");
  const run = join(cs, "CausalSmith", "Run");
  const bundle = join(cs, "doc", "presentation", "fixture");
  for (const dir of [run, bundle, join(root, "Causalean")]) await mkdir(dir, { recursive: true });
  await writeFile(join(cs, "lakefile.toml"), 'name = "CausalSmith"\n');
  await writeFile(join(bundle, "paper_library_index.json"), JSON.stringify({ entries: [], modules: {} }));
  await writeFile(join(bundle, "presentation_crosswalk.json"), JSON.stringify({ lean_subdir: "CausalSmith/Run", entries: [] }));
  return { root, cs, run, bundle };
}
async function check(f: Awaited<ReturnType<typeof fixture>>, file: string, statement = source.trim()) {
  await writeFile(join(f.bundle, "lean_snippets.json"), JSON.stringify({ snippets: { helper: { decl: "helper", file, statement } } }));
  const { stdout } = await execute(resolve(import.meta.dirname, "../node_modules/.bin/tsx"), [
    resolve(import.meta.dirname, "../bin/check_paper_indexes.ts"), "--json", "--no-vs", "--bundle", "fixture",
  ], { cwd: f.cs });
  return JSON.parse(stdout)[0].findings as { severity: string; subject: string }[];
}

it("checks a relocated snippet against its canonical workspace file", async () => {
  const f = await fixture();
  await writeFile(join(f.root, "Causalean", "Helper.lean"), source);
  expect(await check(f, "Causalean/Helper.lean")).toEqual([]);
  expect(await check(f, "Causalean/Helper.lean", "private def helper : Nat := 2"))
    .toContainEqual(expect.objectContaining({ severity: "stale-snippet" }));
});
it("continues to validate ordinary run-relative snippets", async () => {
  const f = await fixture();
  await writeFile(join(f.run, "Helper.lean"), source);
  expect(await check(f, "Helper.lean")).toEqual([]);
  expect(await check(f, "Missing.lean"))
    .toContainEqual(expect.objectContaining({ severity: "missing-file" }));
});
it("rejects a canonical source symlink outside the workspace", async () => {
  const f = await fixture();
  const outside = await mkdtemp(join(tmpdir(), "outside-snippet-")); dirs.push(outside);
  await writeFile(join(outside, "Helper.lean"), source);
  await symlink(join(outside, "Helper.lean"), join(f.root, "Causalean", "Helper.lean"));
  expect(await check(f, "Causalean/Helper.lean"))
    .toContainEqual(expect.objectContaining({ severity: "missing-file" }));
});
