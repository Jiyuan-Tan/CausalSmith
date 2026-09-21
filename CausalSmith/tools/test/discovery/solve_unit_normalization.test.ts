import { describe, expect, it } from "vitest";
import {
  normalizeEmptySolveUnitContainers,
  normalizeStatementReplacementStatuses,
} from "../../src/discovery/solve/unit_io.js";

describe("normalizeEmptySolveUnitContainers", () => {
  it.each([{}, []])("treats empty prose_updates %j as omission", (prose_updates) => {
    const body: { prose_updates?: unknown } = { prose_updates };

    normalizeEmptySolveUnitContainers(body);

    expect(body.prose_updates).toBeUndefined();
  });

  it("preserves nonempty malformed containers for strict schema rejection", () => {
    const body: { prose_updates?: unknown } = { prose_updates: ["unexpected"] };

    normalizeEmptySolveUnitContainers(body);

    expect(body.prose_updates).toEqual(["unexpected"]);
  });
});

describe("normalizeStatementReplacementStatuses", () => {
  it("derives replacement status from citation provenance instead of model output", () => {
    const body = {
      proposed_core_edits: [
        { kind: "statement-replace", proposed: { id: "thm:missing" } },
        { kind: "statement-replace", proposed: { id: "thm:untrusted", status: "proved" } },
        { kind: "statement-replace", proposed: { id: "lem:cited", status: "to-prove", source: { cite: "Paper", locator: "Corollary 2" } } },
        { kind: "definition-replace", proposed: { id: "def:untouched" } },
      ],
    };

    normalizeStatementReplacementStatuses(body);

    expect(body.proposed_core_edits[0].proposed.status).toBe("to-prove");
    expect(body.proposed_core_edits[1].proposed.status).toBe("to-prove");
    expect(body.proposed_core_edits[2].proposed.status).toBe("cited");
    expect(body.proposed_core_edits[3].proposed.status).toBeUndefined();
  });
});
