import { describe, it, expect } from "vitest";
import { PROMOTION_ESCALATION_MARKER } from "../src/presentation/promotion.js";

describe("promotion escalates to the orchestrator instead of guessing", () => {
  it("has a marker the orchestrator can recognize on the halt", () => {
    expect(PROMOTION_ESCALATION_MARKER).toContain("promotion");
  });
});
