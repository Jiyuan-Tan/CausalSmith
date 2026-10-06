import { describe, it, expect } from "vitest";
import { leanRenderCacheKey, renderCacheKey } from "../src/presentation/stages/p1_plan.js";
import { hashEnvBody } from "../src/presentation/tex_anchors.js";

describe("P1 render cache key", () => {
  const r = { statement: "S", refSet: ["b", "a"], priorBody: "p", defects: ["d1"], delivery: null };
  it("empty env hint reproduces the legacy key byte-for-byte", () => {
    const legacy = hashEnvBody(["M", "S", "a,b", "p", "d1", "null", "<cited>"].join("§"));
    expect(renderCacheKey("M", r, "<cited>", "")).toBe(legacy);
  });
  it("a non-empty env hint changes the key", () => {
    expect(renderCacheKey("M", r, "<cited>", "environment: algorithmv")).not.toBe(renderCacheKey("M", r, "<cited>", ""));
  });
});

describe("P1 Lean-render cache key", () => {
  const r: { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[] } =
    { id: "lem:risk", statement: "Let L_theta denote the likelihood ratio.", refSet: ["def:model"] };
  const ctx = { statement: "theorem t : P", referencedDefs: "def model := P" };
  const key = (req = r, context = ctx, kind = "lemma") => leanRenderCacheKey("M", req, context, kind, "<cited>");

  it("invalidates when the NL statement (style/notation input) changes", () => {
    const amended = { ...r, statement: `${r.statement} Let E_0 denote baseline expectation.` };
    expect(key(amended)).not.toBe(key());
  });

  it("invalidates when the Lean statement changes", () => {
    expect(key(r, { ...ctx, statement: "theorem t : Q" })).not.toBe(key());
  });

  it("invalidates when a referenced definition changes", () => {
    expect(key(r, { ...ctx, referencedDefs: "def model := Q" })).not.toBe(key());
  });

  it("invalidates when the kind or a repair's prior body/defects change", () => {
    expect(key(r, ctx, "definition")).not.toBe(key());
    expect(key({ ...r, priorBody: "old", defects: ["Lean fidelity: omits h"] })).not.toBe(key());
  });
});

describe("synth placement: decorated-variant guard", () => {
  it("N_k^{(1)} does not count as a use of bare N_k, but N_k does", async () => {
    const m = await import("../src/presentation/tex_anchors.js");
    const f = (m as unknown as { usesSymbolUndecorated: (t: string, s: string) => boolean }).usesSymbolUndecorated;
    expect(f("the split counts $N_k^{(1)}$ and $N_{ak}^{(1)}$", "N_k")).toBe(false);
    expect(f("the count $N_k$ over the index set", "N_k")).toBe(true);
    expect(f("both $N_k^{(1)}$ and the bare $N_k$", "N_k")).toBe(true);
  });
});
