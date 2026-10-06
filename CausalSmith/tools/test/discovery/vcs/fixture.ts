// A small but complete core: one assumption, one class definition, one symbol, a
// cited leaf, a proved lemma and the headline that uses them. Every field the
// render derives (status, used_by) is present so the fixture is also a valid
// pre-rendered core.
import type { Core } from "../../../src/discovery/core/schema.js";

export function fixtureCore(): Core {
  return {
    qid: "stat_vcs_fixture",
    specialization: "v1",
    cluster: "stat",
    target_estimand: "$\\tau = E[Y(1) - Y(0)]$",
    tldr: "A fixture.",
    symbols: [
      { name: "\\bar d", type: "function", space: "[0,1]", def: "the overlap margin", refs: [] },
      { name: "n", type: "integer", def: "sample size" },
    ],
    assumptions: [
      { id: "ass:overlap", condition: "$\\bar d \\ge \\epsilon$ for some $\\epsilon > 0$", free_symbols: ["\\bar d"], standard: { name: "overlap", cite: "R1983" }, used_by: ["def:class", "lem:helper", "thm:main"] },
    ],
    definitions: [
      { id: "def:class", name: "P", construction: "$\\{P : \\text{ass:overlap holds}\\}$", free_symbols: ["\\bar d"], by_member_properties: ["ass:overlap"] },
    ],
    statements: [
      {
        id: "lem:cited", kind: "lemma", statement: "A published bound: $n^{-1/2}$ rate.", depends_on: [], free_symbols: ["n"],
        status: "cited", source: { cite: "R1983", locator: "Theorem 1" }, justification: "j", gap: "g", consumer: "thm:main",
      },
      {
        id: "lem:helper", kind: "lemma", statement: "Under ass:overlap, the margin is bounded below over def:class.",
        depends_on: ["ass:overlap", "def:class"], free_symbols: ["\\bar d"], status: "proved", proof_tex: "By ass:overlap and the definition of def:class.",
        justification: "j", gap: "g", consumer: "thm:main",
      },
      {
        id: "thm:main", kind: "theorem", statement: "The estimand is identified over def:class at rate $n^{-1/2}$.",
        depends_on: ["ass:overlap", "def:class", "lem:helper", "lem:cited"], free_symbols: ["n", "\\bar d"], status: "proved",
        proof_tex: "Combine lem:helper with lem:cited.", justification: "j", gap: "g", consumer: "c",
      },
    ],
    bibliography: [{ key: "R1983", citation: "Rosenbaum and Rubin (1983)" }],
  } as Core;
}
