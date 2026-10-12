import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { describe, expect, it } from "vitest";
import { runReferee } from "../../../src/discovery/framework/referee.js";
import { generalReviewPayloadValidationError } from "../../../src/discovery/stages/d0_5_general.js";
import type { PipelineContext } from "../../../src/types.js";
import type { StageDeps } from "../../../src/pipeline_support.js";

const ctx = {
  repoRoot: "/tmp/causalsmith-referee-test",
  qid: "stat_test",
  specialization: "v1",
  dryRun: false,
  resume: false,
} as PipelineContext;

describe("stdout referee LaTeX JSON boundary", () => {
  it("removes only an anchored verdict-file patch marker and otherwise requires one JSON document", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-referee-file-"));
    try {
      const body = JSON.stringify({
        referee: "math", verdict: "pass", findings: [], cited_checks: [],
      }, null, 2);
      const runFile = async (name: string, raw: string) => {
        const verdictFile = join(dir, `${name}.json`);
        const deps = {
          runCodex: async () => {
            await writeFile(verdictFile, raw, "utf8");
            return {
              stdout: JSON.stringify({ status: "completed", message: "done", artifacts: [verdictFile] }),
              stderr: "",
            };
          },
        } as unknown as StageDeps;
        return runReferee({
          ctx, deps, stage: "0.5", label: `D0.5 ${name}`,
          prompt: "review", promptSources: ["inline"], model: "test",
          reasoningEffort: "high", verdictFile,
        });
      };
      for (const [name, raw] of [["leading-plus", `+${body}\n`], ["clean", `${body}\n`]]) {
        const result = await runFile(name, raw);
        expect(result.parseError).toBeNull();
        expect(result.json).toMatchObject({ referee: "math", verdict: "pass" });
      }
      const latex = String.raw`+{"referee":"math","verdict":"pass","findings":[{"note":"Uses \(d/\epsilon\)."}],"cited_checks":[]}`;
      const latexResult = await runFile("leading-plus-latex", latex);
      expect((latexResult.json.findings as Array<{ note: string }>)[0].note).toBe(String.raw`Uses \(d/\epsilon\).`);
      await expect(runFile("two-objects", `${body}\n${body}\n`)).rejects.toThrow();
      await expect(runFile("prose-prefix", `note\n${body}\n`)).rejects.toThrow();
      await expect(runFile("suffix", `${body}\ntrailing`)).rejects.toThrow();
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("repairs the round-60 invalid-backslash shape while preserving raw stdout", async () => {
    // Production round 60 failed on the critique's single-backslash inline TeX:
    // `\(d/\epsilon\)` (the first `\(` is an invalid JSON escape).
    const raw = String.raw`{
      "tier":"subfield",
      "salvageable":true,
      "improvement_directive":"Prove the missing comparison.",
      "flagged_conjecture_labels":["clean-temperature-feature-upper"],
      "critique":"The pointwise local \(d/\epsilon\) lower bound remains narrow.",
      "flagship_potential":false,
      "flagship_directive":""
    }`;
    const deps = {
      runCodex: async () => ({ stdout: raw, stderr: "" }),
    } as unknown as StageDeps;

    const result = await runReferee({
      ctx,
      deps,
      stage: "0.5",
      label: "D0.5.G regression",
      prompt: "review this note",
      promptSources: ["inline test"],
      model: "test",
      reasoningEffort: "high",
      leanLsp: false,
      validate: generalReviewPayloadValidationError,
    });

    expect(result.parseError).toBeNull();
    expect(result.raw).toBe(raw);
    expect(result.json.critique).toBe(String.raw`The pointwise local \(d/\epsilon\) lower bound remains narrow.`);
  });

  it("does not accept a repaired but structurally invalid general review", async () => {
    const raw = String.raw`{"tier":"field","critique":"Uses \(d/\epsilon\)."}`;
    const deps = {
      runCodex: async () => ({ stdout: raw, stderr: "" }),
    } as unknown as StageDeps;

    const result = await runReferee({
      ctx,
      deps,
      stage: "0.5",
      label: "D0.5.G invalid regression",
      prompt: "review this note",
      promptSources: ["inline test"],
      model: "test",
      reasoningEffort: "high",
      validate: generalReviewPayloadValidationError,
    });

    expect(result.json.critique).toBe(String.raw`Uses \(d/\epsilon\).`);
    expect(result.parseError).toMatch(/strict schema validation/);
  });
});
