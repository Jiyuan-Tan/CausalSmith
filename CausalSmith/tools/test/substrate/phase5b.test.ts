import { describe, expect, it } from "vitest";
import {
  buildCoordinatorPrompt,
  buildFillerPrompt,
  buildScaffolderPrompt,
} from "../../src/substrate/prompts.js";

describe("Phase 5b prompt configuration", () => {
  it("renders the module header contract in every study prompt", () => {
    const args = {
      requirement: "R", leanDir: "/d", modulePrefix: "M", leanFiles: ["/d/Main.lean"],
      stagingDir: "/stage", lastFailureLog: null,
    };
    const prompts = [
      buildCoordinatorPrompt(args),
      buildScaffolderPrompt({
        slug: "x", requirement: "R", leanDir: "/d", modulePrefix: "M",
        planMarkdown: null, lastReport: null, lastReview: null, buildRounds: 0, buildCap: 1,
      }),
      buildFillerPrompt({
        leanDir: "/d", modulePrefix: "M", prompt: { id: "p", target_decls: [], prompt: "P" },
      }),
    ];
    for (const prompt of prompts) {
      expect(prompt).toContain("exactly one blanket `@[expose] public section`");
      expect(prompt).toMatch(/directory barrel, never the root/i);
      expect(prompt).not.toContain("{{HEADER_CONTRACT}}");
    }
  });
});
