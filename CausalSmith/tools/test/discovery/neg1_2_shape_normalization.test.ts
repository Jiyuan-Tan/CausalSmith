import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { canonicalizeAuthoredCoreShape } from "../../src/discovery/stages/neg1_2_author.js";

describe("D-1.2 authored-core shape normalization", () => {
  it("projects structured seed catalogue entries to titles without changing seed details", () => {
    const seedDetails = [
      { id: "seed:frontier", title: "Matched frontier", motif: "M11+M7" },
      { id: "seed:oracle", title: "Oracle comparison", motif: "M11" },
    ];
    const core = {
      seeds: seedDetails.map(({ id, title, motif }) => ({ id, title, motif })),
      seed_details: seedDetails,
    };

    expect(canonicalizeAuthoredCoreShape(core)).toEqual({
      seeds: ["Matched frontier", "Oracle comparison"],
      seed_details: seedDetails,
    });
  });

  it("canonicalizes dictionary-spelled assumption constants to their ordered names", () => {
    const core = {
      assumptions: [
        { id: "ass:positive-cells", condition: "\\(p >= epsilon_0\\)", constants: { epsilon_0: "\\(epsilon_0 > 0\\)" } },
        { id: "ass:regular-information", condition: "\\[I >= kappa_beta\\]", constants: { kappa_beta: "\\[kappa_beta > 0\\]" } },
      ],
    };

    expect(canonicalizeAuthoredCoreShape(core)).toEqual({
      assumptions: [
        { id: "ass:positive-cells", condition: "\\(\\left(p >= epsilon_0\\right) \\land \\left(epsilon_0 > 0\\right)\\)", constants: ["epsilon_0"] },
        { id: "ass:regular-information", condition: "\\(\\left(I >= kappa_beta\\right) \\land \\left(kappa_beta > 0\\right)\\)", constants: ["kappa_beta"] },
      ],
    });
  });

  it("leaves an already-valid previously passing core unchanged", () => {
    const fixture = JSON.parse(readFileSync(
      new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url),
      "utf8",
    ));
    const before = JSON.stringify(fixture);

    canonicalizeAuthoredCoreShape(fixture);

    expect(JSON.stringify(fixture)).toBe(before);
  });

  it("does not hide malformed non-string dictionaries from the schema gate", () => {
    const core = { assumptions: [{ condition: "\\(p >= epsilon_0\\)", constants: { epsilon_0: 1 } }] };
    expect(canonicalizeAuthoredCoreShape(core)).toBe(core);
  });

  it("does not erase empty or non-formal constraint values", () => {
    const core = { assumptions: [{ condition: "\\(p >= epsilon_0\\)", constants: { epsilon_0: " " } }] };
    expect(canonicalizeAuthoredCoreShape(core)).toBe(core);
    const emptyDelimited = { assumptions: [{ condition: "\\(p >= epsilon_0\\)", constants: { epsilon_0: "\\[   \\]" } }] };
    canonicalizeAuthoredCoreShape(emptyDelimited);
    expect(emptyDelimited.assumptions[0].constants).toEqual({ epsilon_0: "\\[   \\]" });
  });
});
