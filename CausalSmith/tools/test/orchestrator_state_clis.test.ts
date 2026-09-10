import { mkdir, mkdtemp, writeFile, readFile, access, rm, symlink } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { fileURLToPath } from "node:url";
import { beforeEach, describe, expect, it } from "vitest";
import { createInitialState, loadState, saveState } from "../src/state.js";
import { escalationLogPath, readEscalationLog } from "../src/discovery/escalation_log.js";
import type { PipelineContext } from "../src/types.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";

const exec = promisify(execFile);
const __TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TSX_CLI = path.resolve(__TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");
const BIN = (name: string): string => path.resolve(__TOOLS_ROOT, "bin", name);

const QID = "panel_minimal_basis";
const SPEC = "p1_bernoulli";

let repoRoot: string;

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "orch-clis-"));
  // CausalSmith package marker so each bin's findRepoRoot resolves to repoRoot.
  await writeFile(path.join(repoRoot, "lakefile.toml"), `name = "CausalSmith"\n`);
  await saveState(repoRoot, QID, SPEC, createInitialState(QID));
});

function run(bin: string, args: string[]): Promise<{ stdout: string; stderr: string }> {
  return exec(TSX_CLI, [BIN(bin), QID, SPEC, ...args], { cwd: repoRoot, env: { ...process.env } });
}

describe("add_assumption.ts", () => {
  it("appends a schema-valid assumption + a design decision (no hand-edit)", async () => {
    await run("add_assumption.ts", [
      "--label",
      "reg_measurable",
      "--statement",
      "the estimator is measurable in n",
      "--classification",
      "regularity-bookkeeping",
      "--decision",
      "why=discharged from the construction's large-n regime",
    ]);
    const state = await loadState(repoRoot, QID, SPEC);
    expect(state.added_assumptions).toHaveLength(1);
    expect(state.added_assumptions[0]).toMatchObject({
      label: "reg_measurable",
      statement: "the estimator is measurable in n",
      classification: "regularity-bookkeeping",
    });
    expect(state.design_decisions.why).toMatch(/large-n regime/);
  });

  it("replaces an entry with the same label rather than duplicating", async () => {
    await run("add_assumption.ts", ["--label", "a1", "--statement", "first"]);
    await run("add_assumption.ts", ["--label", "a1", "--statement", "second"]);
    const state = await loadState(repoRoot, QID, SPEC);
    expect(state.added_assumptions).toHaveLength(1);
    expect(state.added_assumptions[0].statement).toBe("second");
  });

  it("rejects a bad classification", async () => {
    await expect(
      run("add_assumption.ts", ["--label", "x", "--statement", "y", "--classification", "nonsense"]),
    ).rejects.toThrow();
  });

  // ONE WRITER PER CONCEPT: a substrate-gate needs plan+graph registration, which only gate.ts does.
  // Letting this CLI record the disclosure alone is what stranded `EnvelopeLineC2Data` as a gate
  // that no store knew was a gate (banked `accepted` with undischarged proof-step debt).
  it("REFUSES --classification substrate-gate and routes the caller to gate.ts", async () => {
    await expect(
      run("add_assumption.ts", [
        "--label", "thm:x:SomeGate", "--statement", "y", "--classification", "substrate-gate",
      ]),
    ).rejects.toThrow();
    const state = await loadState(repoRoot, QID, SPEC);
    expect(state.added_assumptions ?? []).toHaveLength(0); // nothing written
  });
});

describe("d0_directive.ts", () => {
  it("refuses before appending when the qid pipeline lock is held", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await withRunHeartbeat(repoRoot, QID, SPEC, async () => {
      await expect(run("d0_directive.ts", [
        "--directive", "must not race an active pipeline",
      ])).rejects.toThrow();
    });
    expect(await readEscalationLog(ctx)).toEqual([]);
  });

  it("appends a standalone directive to the D0 escalation log (no hand-append)", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await mkdir(path.dirname(escalationLogPath(ctx)), { recursive: true });

    await run("d0_directive.ts", ["--directive", "use the plug-in estimator with a Nadaraya-Watson smoother"]);

    const entries = await readEscalationLog(ctx);
    expect(entries).toHaveLength(1);
    expect(entries[0].directive).toMatch(/Nadaraya-Watson/);
  });

  it("scopes a directive to required targets and records a provenance-only entry without pinning the stage", async () => {
    const ctx: PipelineContext = { repoRoot, qid: QID, specialization: SPEC, dryRun: false, resume: true };
    await mkdir(path.dirname(escalationLogPath(ctx)), { recursive: true });
    await run("d0_directive.ts", ["--directive", "tighten the constant", "--require-core-target", "lem:a", "--require-core-target", "thm:b", "--note", "n"]);
    await run("d0_directive.ts", ["--directive", "verdict recorded", "--provenance-only"]);
    const entries = await readEscalationLog(ctx);
    expect(entries).toHaveLength(2);
    expect(entries[0].required_core_targets).toEqual(["lem:a", "thm:b"]);
    expect(entries[0].note).toBe("n");
    expect(entries[1].provenance_only).toBe(true);
    expect((await loadState(repoRoot, QID, SPEC)).stage_completed).toBe("-0.5");
  });
});
