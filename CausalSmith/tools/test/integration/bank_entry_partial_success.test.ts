/**
 * End-to-end integration test for bin/bank_entry.ts and the statement snapshot
 * it records for an accepted run.
 *
 * Asserts:
 *   1. An accepted run is banked at _bank/accepted/<qid>_<spec>/ with its snapshot.
 *   2. A run banked below the accepted tier carries no snapshot.
 *   3. Banking fails, run untouched, when a snapshot exists or cannot be taken.
 */
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { chmod, mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import os from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
const exec = promisify(execFile);
// Use node + tsx/cli.mjs instead of `npx tsx`: on Windows, execFile
// cannot launch the `.cmd` shim and (under Node 20+) `shell: true`
// breaks argument quoting for paths with spaces.
const __TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
const TSX_CLI = path.resolve(__TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");

const __dirname = path.dirname(fileURLToPath(import.meta.url));

let repoRoot: string;
const QID = "panel_partial_success_test";
const SPEC = "v0";

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "bank-partial-"));
  // Minimal CausalSmith package marker so findRepoRoot resolves to repoRoot.
  await writeFile(
    path.join(repoRoot, "lakefile.toml"),
    `name = "CausalSmith"\n`,
    "utf8",
  );
  await mkdir(path.join(repoRoot, "doc", "research", "active", QID), { recursive: true });
  await mkdir(path.join(repoRoot, "doc", "study", "nodes", "open_question"), { recursive: true });
  await mkdir(path.join(repoRoot, "doc", "research", "active", QID, "discovery"), { recursive: true });
  await mkdir(path.join(repoRoot, "doc", "research", "active", QID, "formalization"), { recursive: true });
  await mkdir(path.join(repoRoot, "CausalSmith", "Panel", QID), { recursive: true });
  await writeFile(path.join(repoRoot, "doc", "research", "active", QID, "discovery", "core.json"), JSON.stringify({
    qid: QID, specialization: SPEC, symbols: [], assumptions: [], definitions: [], statements: [],
    target_estimand: "test target", bibliography: [],
  }));
  await writeFile(path.join(repoRoot, "doc", "research", "active", QID, "formalization", "plan.json"), JSON.stringify({
    qid: QID, specialization: SPEC, env: [], nodes: {}, citations: [], feasibility: "formalizable-now",
  }));
  await writeFile(path.join(repoRoot, "doc", "research", "active", QID, "graph.json"), JSON.stringify({
    qid: QID, specialization: SPEC, nodes: [], edges: [],
  }));
  await writeFile(path.join(repoRoot, "CausalSmith", "Panel", QID, "Basic.lean"), "namespace Test\nend Test\n");

  const state = {
    stage_completed: "5",
    lean_subdir: `CausalSmith/Panel/${QID}`,
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: { missing_architecture: false },
  };
  await writeFile(
    path.join(repoRoot, "doc", "research", "active", QID, `${QID}_${SPEC}_state.json`),
    JSON.stringify(state, null, 2) + "\n",
    "utf8",
  );
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

/** A stand-in `lake` first on PATH: `build --no-build` reports everything up to date, and
 *  `exe statement_scan … --out <file>` writes one declaration row — so banking records its statement
 *  snapshot without compiling or reading any Lean. With `upToDate` false it reports a stale build. */
async function withFakeLake(upToDate = true): Promise<NodeJS.ProcessEnv> {
  const bin = path.join(repoRoot, "fakebin");
  await mkdir(bin, { recursive: true });
  const row = JSON.stringify({ name: "Test.x", kind: "theorem", stmt_hash: "1", module: `CausalSmith.Panel.${QID}.Basic`, deps: [] });
  await writeFile(path.join(bin, "lake"), `#!/bin/sh\nif [ "$1" = exe ]; then\n  while [ $# -gt 0 ]; do [ "$1" = --out ] && out=$2; shift; done\n  printf '%s\\n' '${row}' > "$out"\nfi\n`);
  if (!upToDate) await writeFile(path.join(bin, "lake"), "#!/bin/sh\necho 'target is out-of-date' >&2\nexit 1\n");
  await chmod(path.join(bin, "lake"), 0o755);
  return { ...process.env, PATH: `${bin}${path.delimiter}${process.env.PATH ?? ""}` };
}
const SNAPSHOT = "promotion_snapshot.json";

describe("bank_entry.ts banking integration", () => {
  it("banks an accepted run with its statement snapshot", async () => {
    const bankEntryPath = path.resolve(
      __dirname,
      "..",
      "..",
      "bin",
      "bank_entry.ts",
    );
    await exec(
      process.execPath,
      [
        TSX_CLI,
        bankEntryPath,
        "--qid", QID,
        "--spec", SPEC,
        "--tier", "accepted",
        "--reason", "test accepted banking",
      ],
      { cwd: repoRoot, env: await withFakeLake() },
    );

    // 1. Banked dir exists.
    const bankedDir = path.join(
      repoRoot, "doc", "research", "_bank", "accepted", `${QID}_${SPEC}`,
    );
    expect(existsSync(bankedDir)).toBe(true);

    // 2. The accepted entry carries the statement snapshot taken at banking.
    const snap = JSON.parse(await readFile(path.join(bankedDir, SNAPSHOT), "utf8"));
    expect(snap).toMatchObject({ schema: 2, lean_subdir: `CausalSmith/Panel/${QID}`, run: { "Test.x": "1" }, used: {} });
    expect(Object.keys(snap.files)).toEqual([`CausalSmith/Panel/${QID}/Basic.lean`]);
  }, 30_000);

  const bank = async (tier: string, upToDate = true) => exec(
    process.execPath,
    [TSX_CLI, path.resolve(__dirname, "..", "..", "bin", "bank_entry.ts"), "--qid", QID, "--spec", SPEC, "--tier", tier, "--reason", "test"],
    { cwd: repoRoot, env: await withFakeLake(upToDate) },
  );
  const active = () => path.join(repoRoot, "doc", "research", "active", QID);

  it("takes no statement snapshot for a run banked below the accepted tier", async () => {
    await bank("downgraded");
    const bankedDir = path.join(repoRoot, "doc", "research", "_bank", "downgraded", `${QID}_${SPEC}`);
    expect(existsSync(path.join(bankedDir, "README.md"))).toBe(true);
    expect(existsSync(path.join(bankedDir, SNAPSHOT))).toBe(false);
  }, 30_000);

  it("fails the banking, with the run untouched, when a snapshot already exists or cannot be taken", async () => {
    // an existing snapshot is never overwritten
    await writeFile(path.join(active(), SNAPSHOT), "KEEP");
    await expect(bank("accepted")).rejects.toThrow(/written once/);
    expect(await readFile(path.join(active(), SNAPSHOT), "utf8")).toBe("KEEP");
    expect(existsSync(path.join(repoRoot, "doc", "research", "_bank"))).toBe(false);
    expect(JSON.parse(await readFile(path.join(active(), `${QID}_${SPEC}_state.json`), "utf8")).banked).toBeUndefined();
    // the run is not built from its sources: `lake build --no-build` fails
    await rm(path.join(active(), SNAPSHOT));
    await expect(bank("accepted", false)).rejects.toThrow(/is not built from its current sources/);
    expect(existsSync(path.join(repoRoot, "doc", "research", "_bank"))).toBe(false);
  }, 60_000);
});
