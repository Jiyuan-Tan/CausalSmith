import { describe, it, expect } from "vitest";
import {
  runHardGates,
  mapLimit,
  gateLoop,
  parseRubricReview,
  parseJsonArrayLoose,
  parseJsonLoose,
  citingSentences,
  type GateRunners,
  type HardGateInput,
} from "../src/presentation/gates.js";
import { parseAnchoredEnvs } from "../src/presentation/tex_anchors.js";
import { parseBib } from "../src/presentation/citations.js";

const PAPER = `
\\begin{abstract}We prove a bound \\citep{robins1994}.\\end{abstract}
\\section{Introduction}Intro.
\\section{Results}
\\begin{theoremv}{T-1}[Upper bound]
Risk is small.
\\end{theoremv}
\\begin{proof}Step 1. % lean: t1_thm
\\end{proof}
`;

const BIB = parseBib(
  `@article{robins1994, title = {X}, author = {Robins}, year = {1994}\n}`,
);

function makeInput(over: Partial<HardGateInput> = {}): HardGateInput {
  const frozen = new Map(parseAnchoredEnvs(PAPER).map((e) => [e.obj_id, e.body]));
  return {
    paperTex: PAPER,
    layerOrder: [],
    knownObjIds: new Set(["T-1"]),
    frozenBodies: frozen,
    frontMatter: "We prove a bound.",
    frozenEnvsTex: "",
    bibEntries: BIB,
    ...over,
  };
}

const batchVerdict = (verdict: "supported" | "unsupported" | "unverifiable", reason?: string): GateRunners["citationSupportBatch"] =>
  async (pairs) => new Map(pairs.map((p) => [`${p.entry.key}|${p.sentence}`, { verdict, reason }]));

const passingRunners: GateRunners = {
  overclaim: async () => ({ clean: true }),
  citationSupportBatch: batchVerdict("supported"),
};

describe("hard gates", () => {
  it("passes on a clean paper", async () => {
    expect(await runHardGates(makeInput(), passingRunners)).toEqual([]);
  });

  it("drops an overclaim flag whose fix only strips the obj: prefix and restores the prefix otherwise", async () => {
    const sentence = "\\Cref{obj:T-1} shows the bound, see \\cref{obj:T-1}.";
    const noop = await runHardGates(makeInput(), {
      ...passingRunners,
      overclaim: async () => ({ clean: false, flags: [{ sentence, fix: "\\Cref{T-1} shows the bound, see \\cref{T-1}." }] }),
    });
    expect(noop.some((p) => p.gate === "overclaim")).toBe(false);
    const real = await runHardGates(makeInput(), {
      ...passingRunners,
      overclaim: async () => ({ clean: false, flags: [{ sentence, fix: "\\Cref{T-1} gives the bound, see \\cref{T-1}." }] }),
    });
    const flag = real.find((p) => p.gate === "overclaim");
    expect(flag?.detail).toContain("→ \\Cref{obj:T-1} gives the bound, see \\cref{obj:T-1}.");
  });

  it("a single unsupported / overclaim verdict fails the run", async () => {
    const oc = await runHardGates(makeInput(), {
      ...passingRunners,
      overclaim: async () => ({ clean: false, flags: [{ sentence: "We solve everything." }] }),
    });
    expect(oc.some((p) => p.gate === "overclaim")).toBe(true);

    const cs = await runHardGates(makeInput(), {
      ...passingRunners,
      citationSupportBatch: batchVerdict("unsupported", "overgeneralized"),
    });
    expect(cs.some((p) => p.gate === "citation-support")).toBe(true);
  });

  it("a pair the batch auditor returned no verdict for is advisory-unverifiable, never silently supported", async () => {
    const problems = await runHardGates(makeInput(), {
      ...passingRunners,
      citationSupportBatch: async () => new Map(),
    });
    expect(problems.some((p) => p.gate === "citation-unverifiable" && p.detail.includes("no verdict"))).toBe(true);
    expect(problems.some((p) => p.gate === "citation-support")).toBe(false);
  });

  it("flags citations outside the pool and frozen drift", async () => {
    const stray = await runHardGates(
      makeInput({ paperTex: PAPER + "\\citet{ghost2020}" }),
      passingRunners,
    );
    expect(stray.some((p) => p.gate === "cite-pool" && p.detail.includes("ghost2020"))).toBe(true);

    const drifted = await runHardGates(
      makeInput({ paperTex: PAPER.replace("Risk is small.", "Risk is tiny.") }),
      passingRunners,
    );
    expect(drifted.some((p) => p.gate === "frozen-drift")).toBe(true);
  });

  it("hard-fails when a notation-table symbol is defined after its first formal use", async () => {
    const orderPaper = PAPER + String.raw`
\begin{assumptionv}{ass:forward-axis-model}[Forward axis]
\[(X,Y)^\top=\sum_j u_jS_j.\]
\end{assumptionv}
\begin{definitionv}{def:forward-cumulant-map}[Forward map]
Let \(u_j\) be the forward loading vector.
\end{definitionv}`;
    const frozen = new Map(parseAnchoredEnvs(orderPaper).map((e) => [e.obj_id, e.body]));
    const problems = await runHardGates(
      makeInput({
        paperTex: orderPaper,
        layerOrder: ["def:forward-cumulant-map", "ass:forward-axis-model"],
        knownObjIds: new Set(["T-1", "ass:forward-axis-model", "def:forward-cumulant-map"]),
        frozenBodies: frozen,
      }),
      passingRunners,
    );
    expect(problems).toContainEqual(expect.objectContaining({
      gate: "frozen-layer-order",
      objId: "def:forward-cumulant-map",
    }));
  });
});

describe("gate loop", () => {
  it("revises until clean within the cap", async () => {
    let failures = 2;
    const r = await gateLoop({
      maxRounds: 3,
      run: async () => (failures > 0 ? [{ gate: "x", detail: "d" }] : []),
      revise: async () => {
        failures--;
      },
    });
    expect(r.ok).toBe(true);
    expect(r.rounds).toBe(2);
  });

  it("halts with problems after max rounds", async () => {
    let revisions = 0;
    const r = await gateLoop({
      maxRounds: 3,
      run: async () => [{ gate: "x", detail: "persistent" }],
      revise: async () => {
        revisions++;
      },
    });
    expect(r.ok).toBe(false);
    expect(revisions).toBe(3);
    expect(r.problems[0].detail).toBe("persistent");
  });
});

describe("helpers", () => {
  it("parseJsonLoose finds JSON in chatter", () => {
    expect(parseJsonLoose('blah\n{"verdict": "drift"}\nbye')).toEqual({ verdict: "drift" });
    expect(parseJsonLoose(String.raw`{"verdict":"faithful","detail":"Matches \\(m\\ge1\\)."}`)).toEqual({
      verdict: "faithful",
      detail: String.raw`Matches \(m\ge1\).`,
    });
    expect(parseJsonLoose("no json")).toBeNull();
  });

  it("parseJsonLoose repairs lone LaTeX escapes without corrupting valid escaped LaTeX", () => {
    const mixed = String.raw`{"score":8.2,"issue":"valid \\(x\\)","fix":"lone \(p_k=0\)"}`;
    expect(parseJsonLoose(mixed)).toEqual({
      score: 8.2,
      issue: String.raw`valid \(x\)`,
      fix: String.raw`lone \(p_k=0\)`,
    });
  });

  it("parseJsonArrayLoose extracts array replies parseJsonLoose structurally cannot", () => {
    // The live P1 synthesis failure (2026-08-26): a well-formed array reply, sliced by the
    // object-only parser from first `{` to last `}`, degraded to its FIRST element — so
    // Array.isArray failed and all 11 codex batches were burned as "unparseable".
    const live = String.raw`[{"symbols":["\\mathcal D_d^{\\mathrm{bin}}(\\epsilon)","\\Phi_M"],"title":"Binary source classes","body":"Let \\(\\mathcal D_d^{\\mathrm{bin}}(\\epsilon)\\) be the class."}]`;
    const groups = parseJsonArrayLoose(live) as { symbols: string[]; body: string }[];
    expect(Array.isArray(groups)).toBe(true);
    expect(groups).toHaveLength(1);
    expect(groups[0].symbols).toEqual([
      String.raw`\mathcal D_d^{\mathrm{bin}}(\epsilon)`,
      String.raw`\Phi_M`,
    ]);
    // Multi-group array inside codex chatter + fences; lone-escape repair applies per string.
    const fenced = 'Sure.\n```json\n[{"symbols":["K_n"],"body":"lone \\(K_n\\)"},{"symbols":["M"],"body":"cap"}]\n```\ndone';
    expect(parseJsonArrayLoose(fenced)).toEqual([
      { symbols: ["K_n"], body: String.raw`lone \(K_n\)` },
      { symbols: ["M"], body: "cap" },
    ]);
    // A non-JSON bracket pair in prose before the real array does not poison the
    // scan; object-only and array-free replies return null, never a coerced value.
    expect(parseJsonArrayLoose('see [note 3] above\n[{"symbols":["x"],"body":"b"}] tail')).toEqual([
      { symbols: ["x"], body: "b" },
    ]);
    expect(parseJsonArrayLoose('{"verdict":"drift"}')).toBeNull();
    expect(parseJsonArrayLoose("no json")).toBeNull();
  });

  it("citingSentences pairs sentences with keys", () => {
    const s = citingSentences("First fact \\citep{a1}. Second sentence. Third \\citet{b2, c3}.");
    expect(s).toHaveLength(2);
    expect(s[1].keys).toEqual(["b2", "c3"]);
  });
});

describe("parseRubricReview (P3 rubric JSON boundary)", () => {
  it("accepts a well-formed review and defaults weaknesses/defects", () => {
    expect(parseRubricReview({ scores: { rigor: 7, novelty: 6.5 } }))
      .toEqual({ scores: { rigor: 7, novelty: 6.5 }, weaknesses: [], defects: [] });
  });
  it("carries the defects list and rejects a malformed one", () => {
    expect(parseRubricReview({ scores: { rigor: 7 }, defects: ["placeholder text in a label"] }))
      .toEqual({ scores: { rigor: 7 }, weaknesses: [], defects: ["placeholder text in a label"] });
    expect(parseRubricReview({ scores: { rigor: 7 }, defects: "not an array" })).toBeNull();
  });
  it("rejects string scores (previously became NaN and passed)", () => {
    expect(parseRubricReview({ scores: { rigor: "7/10" }, weaknesses: [] })).toBeNull();
  });
  it("rejects empty/missing scores and non-objects", () => {
    expect(parseRubricReview({ scores: {} })).toBeNull();
    expect(parseRubricReview(null)).toBeNull();
    expect(parseRubricReview({ weaknesses: ["w"] })).toBeNull();
  });
  it("rejects non-string weaknesses", () => {
    expect(parseRubricReview({ scores: { a: 5 }, weaknesses: [{ w: 1 }] })).toBeNull();
  });
  it("parseRubricReview filters legacy malformed cache entries", () => {
    const cached: unknown[] = [{ scores: { rigor: "7/10" } }, { scores: { rigor: 7 } }];
    const valid = cached.map((v) => parseRubricReview(v)).filter(Boolean);
    expect(valid).toEqual([{ scores: { rigor: 7 }, weaknesses: [], defects: [] }]);
  });
});

describe("parseJsonLoose escape defense (shared with the D-stage normalizer)", () => {
  it("repairs the silent b/f/r/t collision class before parsing", () => {
    // Corpus case (panel_ppml gate cache): an under-escaped `\to` decodes to a
    // tab under plain JSON.parse; the raw-byte normalizer must restore it.
    const reply =
      "verdict follows\n" + String.raw`{"weaknesses":["type should be (\Omega_N \to \mathbb R)"]}`;
    expect(parseJsonLoose(reply)).toEqual({
      weaknesses: [String.raw`type should be (\Omega_N \to \mathbb R)`],
    });
  });

  it("repairs control characters that arrive pre-encoded as unicode escapes", () => {
    // The \u0009-channel: raw-byte normalization must preserve a valid escape,
    // so the post-parse deep repair restores the TeX command prefix.
    const reply = String.raw`{"detail":"Theorem \\ref{a} vs \u0009heta"}`;
    expect(parseJsonLoose(reply)).toEqual({
      detail: String.raw`Theorem \ref{a} vs \theta`,
    });
  });
});


describe("mapLimit failure recovery", () => {
  it("stops scheduling after failure and drains in-flight work before rejecting", async () => {
    const started: number[] = [];
    let release!: () => void;
    const pending = new Promise<void>((resolve) => { release = resolve; });
    let drained = false;
    const run = mapLimit([0, 1, 2, 3], 2, async (i) => {
      started.push(i);
      if (i === 0) throw new Error("failed");
      await pending;
      drained = true;
      return i;
    });
    let settled = false;
    const checked = expect(run).rejects.toThrow("failed").then(() => { settled = true; });
    await new Promise<void>((resolve) => setImmediate(resolve));
    expect(started).toEqual([0, 1]);
    expect(settled).toBe(false);
    release();
    await checked;
    expect(drained).toBe(true);
    expect(started).toEqual([0, 1]);
  });
});
