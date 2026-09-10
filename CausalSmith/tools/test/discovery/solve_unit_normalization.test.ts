import { describe, expect, it } from "vitest";
import { normalizeStatementReplacementStatuses } from "../../src/discovery/solve/unit_io.js";

describe("normalizeStatementReplacementStatuses", () => {
  it("deterministically keeps statement replacements to-prove", () => {
    const body = {
      proposed_core_edits: [
        { kind: "statement-replace", proposed: { id: "thm:missing" } },
        { kind: "statement-replace", proposed: { id: "thm:untrusted", status: "proved" } },
        { kind: "definition-replace", proposed: { id: "def:untouched" } },
      ],
    };

    normalizeStatementReplacementStatuses(body);

    expect(body.proposed_core_edits[0].proposed.status).toBe("to-prove");
    expect(body.proposed_core_edits[1].proposed.status).toBe("to-prove");
    expect(body.proposed_core_edits[2].proposed.status).toBeUndefined();
  });
});
