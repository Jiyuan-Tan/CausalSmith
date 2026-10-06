import { describe, expect, it } from "vitest";
import { jsonForModelPrompt } from "../../src/discovery/core/prompt_serialization.js";

describe("model-prompt JSON serialization", () => {
  it("makes control boundaries explicit without changing parsed content", () => {
    const artifact = {
      proof_tex: "\\begin{cases}\nu/(1-q_a)\\end{cases}",
      literalNu: "\\nu",
      literalFrac: "\\frac{a}{b}",
      mixed: "literal slash \\\nnext",
    };
    const rendered = jsonForModelPrompt(artifact);
    expect(rendered).toContain("cases}\\u000Au/(1-q_a)");
    expect(rendered).not.toContain("cases}\\nu/(1-q_a)");
    expect(rendered).toContain("\\\\nu");
    expect(rendered).toContain("\\\\frac");
    expect(JSON.parse(rendered)).toEqual(artifact);
  });
});
