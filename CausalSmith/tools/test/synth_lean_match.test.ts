import { describe, it, expect } from "vitest";
import { conceptKey, resolveSymbolHomes } from "../src/presentation/synth_lean_match.js";
import type { SymbolCluster } from "../src/formalization/crosswalk.js";

const NS = "CausalSmith.Stat.Run";
const decls = new Map([
  [`${NS}.summaryRadius`, { file: "Basic.lean", line: 40, kind: "def" }],
  [`${NS}.GapScaleDomain`, { file: "Helpers/Domains.lean", line: 12, kind: "structure" }],
  [`${NS}.JacksonTuning`, { file: "Helpers/Estimator.lean", line: 7, kind: "structure" }],
  [`${NS}.splitCellCount`, { file: "Helpers/Estimator.lean", line: 22, kind: "def" }],
  // a lemma ABOUT the radius — never the definition's home
  [`${NS}.summaryRadius_nonneg`, { file: "Helpers/Endpoint.lean", line: 189, kind: "theorem" }],
  [`${NS}.mse`, { file: "Basic.lean", line: 10, kind: "def" }],
  // two def-like decls sharing a short name → ambiguous
  [`${NS}.A.kernelWeight`, { file: "A.lean", line: 1, kind: "def" }],
  [`${NS}.B.kernelWeight`, { file: "B.lean", line: 1, kind: "def" }],
]);
const clusters: SymbolCluster[] = [
  // members carry the header name as written (short), the way buildSymbolClusters reports them
  { symbol: "kappa", members: [
    { decl: "JacksonTuning", declKind: "structure", file: "Helpers/Estimator.lean", line: 7 },
  ] },
  { symbol: "D_0", members: [
    { decl: "JacksonTuning", declKind: "structure", file: "Helpers/Estimator.lean", line: 7 },
  ] },
  { symbol: "lambda_n", members: [
    // only a lemma realizes it — a tag alone does not make a lemma a definition's home
    { decl: `${NS}.latticeLaw_tight`, declKind: "theorem", file: "Helpers/Lattice.lean", line: 90 },
  ] },
  // case-distinct siblings: the notation key folds case, the cluster spelling decides
  { symbol: "pi", members: [{ decl: "policy", declKind: "def", file: "P.lean", line: 3 }] },
  { symbol: "Pi", members: [{ decl: "policyClass", declKind: "def", file: "P.lean", line: 9 }] },
  // a tag whose def-like member the module index cannot name
  { symbol: "omega", members: [{ decl: "ghostWeight", declKind: "def", file: "G.lean", line: 1 }] },
];
const declsWithPolicies = new Map([
  ...decls,
  [`${NS}.policy`, { file: "P.lean", line: 3, kind: "def" }],
  ["policy", { file: "P.lean", line: 3, kind: "def" }],
  [`${NS}.policyClass`, { file: "P.lean", line: 9, kind: "def" }],
]);

describe("conceptKey", () => {
  it("keeps text-font contents and drops the rest of the LaTeX", () => {
    expect(conceptKey("\\operatorname{summaryRadius}")).toBe("summaryradius");
    expect(conceptKey("\\text{gap-scale domain}")).toBe("gapscaledomain");
    expect(conceptKey("Centered estimator \\(\\widehat\\tau_{\\mathrm{ctr}}\\)")).toBe("centeredestimator");
    expect(conceptKey("Split cell counts $N^{(0)}_{aky}$")).toBe("splitcellcounts");
  });
});

describe("resolveSymbolHomes", () => {
  it("resolves an @realizes-tagged symbol to the def-like member under the index's qualified name, grouping a structure's fields", () => {
    const withShort = new Map([...decls, ["JacksonTuning", { file: "Helpers/Estimator.lean", line: 7, kind: "structure" }]]);
    const { homes, unresolved } = resolveSymbolHomes(["\\kappa", "D_0"], clusters, withShort);
    expect(unresolved).toEqual([]);
    expect(homes).toEqual([{ decl: `${NS}.JacksonTuning`, file: "Helpers/Estimator.lean", line: 7, decl_kind: "structure", symbols: ["\\kappa", "D_0"] }]);
  });

  it("joins a tag-resolved and a name-resolved symbol of one declaration into one home", () => {
    const withShort = new Map([...decls, ["JacksonTuning", { file: "Helpers/Estimator.lean", line: 7, kind: "structure" }]]);
    const { homes } = resolveSymbolHomes(["\\kappa", "\\text{Jackson tuning}"], clusters, withShort);
    expect(homes.map((h) => [h.decl, h.symbols])).toEqual([[`${NS}.JacksonTuning`, ["\\kappa", "\\text{Jackson tuning}"]]]);
  });

  it("resolves a Lean identifier set in a text font to the same-named def-like declaration", () => {
    const { homes } = resolveSymbolHomes(["\\operatorname{summaryRadius}", "\\text{gap-scale domain}"], [], decls);
    expect(homes.map((h) => [h.decl, h.symbols])).toEqual([
      [`${NS}.summaryRadius`, ["\\operatorname{summaryRadius}"]],
      [`${NS}.GapScaleDomain`, ["\\text{gap-scale domain}"]],
    ]);
  });

  it("leaves unresolved what no tag and no unique same-named definition covers", () => {
    const symbols = ["\\lambda_n", "\\mathcal H^\\beta(L)", "\\text{split cell counts}", "\\mathrm{mse}", "\\operatorname{kernelWeight}", "\\omega"];
    const { homes, unresolved } = resolveSymbolHomes(symbols, clusters, decls);
    expect(homes).toEqual([]);
    // lemma-only tag; no decl; plural/singular gap; key below the minimum length; ambiguous short
    // name; tagged member absent from the module index
    expect(unresolved).toEqual(symbols);
  });

  it("matches tags case-sensitively: `\\Pi` never homes on the `pi` cluster", () => {
    expect(resolveSymbolHomes(["\\Pi"], clusters, declsWithPolicies).homes[0].decl).toBe(`${NS}.policyClass`);
    expect(resolveSymbolHomes(["\\pi"], clusters, declsWithPolicies).homes[0].decl).toBe(`${NS}.policy`);
    const onlyLower = clusters.filter((c) => c.symbol !== "Pi");
    expect(resolveSymbolHomes(["\\Pi"], onlyLower, declsWithPolicies).homes).toEqual([]);
  });

  it("names the family for a use with arguments and refuses a declaration a paper env already presents", () => {
    expect(resolveSymbolHomes(["\\operatorname{summaryRadius}(S)"], [], decls).homes[0].decl).toBe(`${NS}.summaryRadius`);
    // presented names are compared by their short form, whichever form the graph node carries
    const r = resolveSymbolHomes(["\\operatorname{summaryRadius}(S)", "\\kappa"], clusters, new Map([...decls, ["JacksonTuning", { file: "Helpers/Estimator.lean", line: 7, kind: "structure" }]]), new Set(["summaryRadius"]));
    expect(r.homes.map((h) => h.decl)).toEqual([`${NS}.JacksonTuning`]);
    expect(r.unresolved).toEqual(["\\operatorname{summaryRadius}(S)"]);
    expect(r.presentedBy.get("\\operatorname{summaryRadius}(S)")).toBe(`${NS}.summaryRadius`);
  });

  it("never homes a definition on a theorem, even when the key collides", () => {
    const { homes } = resolveSymbolHomes(["\\operatorname{summaryRadius}"], [], decls);
    expect(homes[0].decl).toBe(`${NS}.summaryRadius`);
  });
});
