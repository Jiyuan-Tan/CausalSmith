import { mkdtemp } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { CAP_GATE_FLAGS, clearCapGate } from "../src/cap_gates.js";
import { parseArgsForTest } from "../src/cli.js";
import { runPipeline } from "../src/pipeline.js";
import { createInitialState, loadState, saveState } from "../src/state.js";
import type { StateJson } from "../src/types.js";

describe("cap_gates registry", () => {
  it("clears each flag and resets its paired counter", () => {
    const flags = {
      stage_neg1_fallback: "pivot exhausted",
      neg1_env_failure_retries: 3,
    } as unknown as StateJson["flags"];

    clearCapGate(flags, "stage_neg1_fallback");
    expect(flags.stage_neg1_fallback).toBeNull();
    expect(flags.neg1_env_failure_retries).toBe(0);
  });

  it("throws on an unknown gate name", () => {
    expect(() => clearCapGate({} as unknown as StateJson["flags"], "not_a_gate")).toThrow(/unknown gate/);
  });

  it("exposes every known gate flag", () => {
    expect([...CAP_GATE_FLAGS].sort()).toEqual(["d0_loop_cap_hit", "proof_loop_cap_hit", "stage_neg1_fallback"]);
  });
});

describe("parseArgs --clear-gate", () => {
  it("parses repeated --clear-gate on --resume", () => {
    const a = parseArgsForTest([
      "--resume",
      "--clear-gate",
      "stage_neg1_fallback",
      "--clear-gate",
      "proof_loop_cap_hit",
      "pid_foo",
      "v1",
    ]);
    expect(a.clearGates).toEqual(["stage_neg1_fallback", "proof_loop_cap_hit"]);
  });

  it("rejects --clear-gate without --resume", () => {
    expect(() => parseArgsForTest(["--clear-gate", "proof_loop_cap_hit", "pid_foo", "v1"])).toThrow(
      /requires --resume/,
    );
  });

  it("rejects an unknown gate name at parse time", () => {
    expect(() => parseArgsForTest(["--resume", "--clear-gate", "bogus", "pid_foo", "v1"])).toThrow(/unknown gate/);
  });

  it("leaves clearGates undefined when the flag is absent", () => {
    const a = parseArgsForTest(["--resume", "pid_foo", "v1"]);
    expect(a.clearGates).toBeUndefined();
  });
});

describe("runPipeline resume-time cap-gate clear", () => {
  const qid = "panel_minimal_basis";
  const spec = "p1_bernoulli";

  async function seedBlockedState(): Promise<string> {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-capgate-"));
    const state = createInitialState(qid);
    state.stage_completed = "2";
    state.flags.stage_neg1_fallback = "pivot exhausted";
    state.flags.neg1_env_failure_retries = 3;
    await saveState(repoRoot, qid, spec, state);
    return repoRoot;
  }

  it("blocks resume while the gate flag is set", async () => {
    const repoRoot = await seedBlockedState();
    const blocked = await runPipeline({ repoRoot, qid, specialization: spec, resume: true, dryRun: true });
    // Gate closed → stage does not advance, flag persists.
    expect(blocked.stage_completed).toBe("2");
    expect(blocked.flags.stage_neg1_fallback).toBeTruthy();
  });

  it("clears the flag + resets the counter and proceeds when --clear-gate is passed", async () => {
    const repoRoot = await seedBlockedState();
    const cleared = await runPipeline(
      { repoRoot, qid, specialization: spec, resume: true, dryRun: true },
      undefined,
      { clearGates: ["stage_neg1_fallback"] },
    );
    expect(cleared.flags.stage_neg1_fallback).toBeNull();
    expect(cleared.flags.neg1_env_failure_retries).toBe(0);
    expect(cleared.stage_completed).toBe("5");

    // Persisted, not just in-memory.
    const onDisk = await loadState(repoRoot, qid, spec);
    expect(onDisk.flags.stage_neg1_fallback).toBeNull();
  });
});
