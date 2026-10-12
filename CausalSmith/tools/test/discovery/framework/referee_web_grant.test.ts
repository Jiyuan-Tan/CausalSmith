// The referee web grant. D-0.5 relies on codex's default-on hosted search; D0.5.G grades a
// note against PUBLISHED work and pins the grant explicitly. These tests pin that an unset
// grant is not forwarded and that an explicit grant or denial is.
import { describe, expect, it } from "vitest";
import { runReferee } from "../../../src/discovery/framework/referee.js";
import { MODEL_PLAN } from "../../../src/constants.js";
import type { PipelineContext } from "../../../src/types.js";
import type { StageDeps } from "../../../src/pipeline_support.js";

const ctx = {
  repoRoot: "/tmp/causalsmith-referee-web-test",
  qid: "stat_test",
  specialization: "v1",
  dryRun: false,
  resume: false,
} as PipelineContext;

const verdict = JSON.stringify({
  tier: "field",
  salvageable: false,
  flagged_conjecture_labels: [],
  critique: "Meets the field floor on the proved class.",
  flagship_potential: false,
  flagship_directive: "",
});

/** Capture what the codex runner is handed. */
function codexDeps(inputs: Array<Record<string, unknown>>): StageDeps {
  return {
    runCodex: async (input: Record<string, unknown>) => {
      inputs.push(input);
      return { stdout: verdict, stderr: "" };
    },
  } as unknown as StageDeps;
}

describe("runReferee web grant on the codex runner", () => {
  async function run(webSearch?: boolean): Promise<Record<string, unknown>> {
    const inputs: Array<Record<string, unknown>> = [];
    await runReferee({
      ctx, deps: codexDeps(inputs), stage: "0.5", label: "codex referee",
      prompt: "review", promptSources: ["inline"], model: "gpt-5.6-sol",
      reasoningEffort: "high", leanLsp: false,
      ...(webSearch === undefined ? {} : { webSearch }),
    });
    return inputs[0]!;
  }

  it("leaves codex's default-on search alone when the caller says nothing", async () => {
    // Load-bearing: D-0.5's prompt instructs citation verification and relies on this
    // default. Mapping unset to `false` would silently take the web away from it.
    expect(await run()).not.toHaveProperty("webSearch");
  });

  it("forwards an explicit grant, pinning intent against a change of default", async () => {
    expect(await run(true)).toMatchObject({ webSearch: true, reasoningEffort: "high" });
  });

  it("forwards an explicit denial, so a hermetic codex referee is still expressible", async () => {
    expect(await run(false)).toMatchObject({ webSearch: false });
  });
});

describe("D0.5.G runner configuration", () => {
  it("judges on codex at high effort", () => {
    expect(MODEL_PLAN.stage0_5_general).toMatchObject({ runner: "codex", effort: "high" });
  });
});
