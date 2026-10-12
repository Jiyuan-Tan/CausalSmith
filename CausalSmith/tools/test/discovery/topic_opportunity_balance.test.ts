import { describe, expect, it } from "vitest";
import { assembleNeg1_2AuthorPrompt } from "../../src/discovery/stages/neg1_2_author.js";
import { shouldUseLeanRender } from "../../src/presentation/stages/p1_plan.js";

describe("topic opportunity contract", () => {
  it("assembles the author prompt from its parts and never Lean-renders an undelivered remark", () => {
    const assembled = assembleNeg1_2AuthorPrompt({
      head: "HEAD-BLOCK",
      core: "CORE-BLOCK",
      brief: "brief",
      contextBlocks: "=== STAGE -1.1 GAPS CONTEXT ===\n{}",
      corePath: "/tmp/proto_core.json",
    });
    expect(assembled).toContain("HEAD-BLOCK");
    expect(assembled).toContain("CORE-BLOCK");
    expect(assembled).toContain("STAGE -1.1 GAPS CONTEXT");
    // An undelivered remark is never rendered from a Lean signature.
    expect(shouldUseLeanRender("undelivered", true)).toBe(false);
    expect(shouldUseLeanRender("deliver", true)).toBe(true);
  });
});
