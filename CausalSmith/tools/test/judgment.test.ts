import { describe, expect, it } from "vitest";
import { extractJsonObject, reviewResultSchema } from "../src/judgment.js";

describe("reviewResultSchema", () => {
  it("accepts `accept` as a synonym of `pass`", () => {
    const parsed = reviewResultSchema.parse({ status: "accept", notes: "reuse decisions are sound" });

    expect(parsed.status).toBe("accept");
  });

  it("accepts a revise result and keeps fields it does not declare", () => {
    const parsed = reviewResultSchema.parse({
      status: "revise",
      classification: "correctness",
      perItemFindings: [
        {
          label: "Theorem 1",
          verdict: "correctness",
          one_line: "inverse step needs a rank hypothesis",
        },
      ],
      verbatim_critique: "Add the missing rank hypothesis and cite it in the proof.",
      journal_recommendations: [],
    });

    expect(parsed.status).toBe("revise");
    expect((parsed as Record<string, unknown>).journal_recommendations).toEqual([]);
  });
});

describe("extractJsonObject", () => {
  it("parses a pure JSON object", () => {
    const out = extractJsonObject('{"route":"stage_2","reason":"ok"}');
    expect(out).toEqual({ route: "stage_2", reason: "ok" });
  });

  it("parses JSON preceded by prose", () => {
    const text = 'Some preamble explaining the diagnosis.\n\n{"route":"stage_0","reason":"x"}';
    expect(extractJsonObject(text)).toEqual({ route: "stage_0", reason: "x" });
  });

  it("skips accidentally balanced braces in prose (the {Z=z_l} regression)", () => {
    // Reproduces the production failure: codex's prose contained a backticked
    // Lean set `{Z=z_l}` BEFORE the real JSON. The legacy extractor latched
    // onto the first balanced pair and failed JSON.parse at position 1 (Z
    // is not a quoted key). The fix tries successive `{` positions until one
    // parses successfully.
    const text =
      "L-8 cites P-9 (partition by `{Z=z_l}` and integrability) which the Lean signature dropped.\n\n" +
      '{"route":"stage_2","reason":"Case 4b (encoding drift)","proposed_action":"Re-scaffold."}';
    expect(extractJsonObject(text)).toEqual({
      route: "stage_2",
      reason: "Case 4b (encoding drift)",
      proposed_action: "Re-scaffold.",
    });
  });

  it("skips multiple accidental balanced-brace prose runs before the real JSON", () => {
    const text =
      "Prose with `{a}` and another `{b=c}` and `{x | P x}` ahead.\n" +
      '{"route":"stage_1","reason":"r"}';
    expect(extractJsonObject(text)).toEqual({ route: "stage_1", reason: "r" });
  });

  it("parses JSON inside a fenced code block", () => {
    const text = "Here is the verdict:\n```json\n{\"route\":\"user\"}\n```\nDone.";
    expect(extractJsonObject(text)).toEqual({ route: "user" });
  });

  it("returns the first valid JSON when multiple JSON objects are present", () => {
    const text = '{"route":"stage_0"}\n\nlater: {"route":"stage_2"}';
    expect(extractJsonObject(text)).toEqual({ route: "stage_0" });
  });

  it("throws when no JSON object is present", () => {
    expect(() => extractJsonObject("plain prose, no braces")).toThrow();
  });

  it("surfaces the underlying JSON.parse error when all candidates fail", () => {
    // No balanced `{...}` parses; legacy first-to-last fallback also fails.
    expect(() => extractJsonObject("foo {bar} baz")).toThrow();
  });
});
