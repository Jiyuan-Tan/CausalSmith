import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, writeFile, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { proofAuditCacheKey, proofAuditFormalContext, proofAuditSemanticNotation, runProofAudit } from "../src/presentation/audit.js";
import { parseAnchoredEnvs, hashEnvBody } from "../src/presentation/tex_anchors.js";
import { PRESENTATION_PROSE_POLICY_VERSION, promptFingerprint } from "../src/presentation/prompt_io.js";
import type { StageIO } from "../src/presentation/pipeline.js";

/**
 * Mechanical-layer test for the P2 proof equivalence audit (runProofAudit). Drives the full
 * judge → repair → persist → halt machinery with a STUB codex judge and a STUB render hook: the
 * verdict is keyed on whether the proof body already says "REFINED", so the loop is exercised
 * statelessly (no real Lean / codex).
 *   • thm_ok  — judged faithful first time              → unchanged, no problem
 *   • thm_fix — unfaithful, then faithful after repair  → file rewritten, no problem
 *   • thm_bad — unfaithful even after repair            → last attempt persisted, one problem
 */

import { canonicalizeProofTitle, existingProofForP2 } from "../src/presentation/stages/p2_draft.js";

describe("canonicalizeProofTitle", () => {
  it("rewrites free-form, prefixless, and missing titles to the canonical attributable form", () => {
    const canon = "\\begin{proof}[Proof of \\cref{obj:lem:x}]body\\end{proof}";
    expect(canonicalizeProofTitle("lem:x", "\\begin{proof}body\\end{proof}")).toBe(canon);
    expect(canonicalizeProofTitle("lem:x", "\\begin{proof}[Free-form title]body\\end{proof}")).toBe(canon);
    expect(canonicalizeProofTitle("lem:x", "\\begin{proof}[Proof of \\cref{lem:x}]body\\end{proof}")).toBe(canon);
    expect(canonicalizeProofTitle("lem:x", canon)).toBe(canon); // idempotent
  });
});

function proofBody(id: string, refined = false): string {
  // Refined proofs are persisted with the CANONICAL title (the refiner may rewrite
  // or drop it, making the proof unattributable and invisible to the placement lint).
  const title = refined ? `[Proof of \\cref{obj:${id}}]` : "";
  return `\\begin{proof}${title}${refined ? "REFINED" : "draft"} proof of ${id}\\end{proof}`;
}

// Stub judge: identifies the target by the obj_id embedded in the prompt. thm_bad is always
// unfaithful (with a [missing-step] issue → promotable); thm_fix is unfaithful until its body is
// the REFINED one.
const stubRunCodex = async ({ prompt }: { prompt: string }) => {
  // The prompt's output schema names the judged target; the catalogue names every sibling.
  const id = prompt.match(/"theorem": "(thm_\w+)"/)?.[1] ?? ["thm_ok", "thm_fix", "thm_bad"].find((x) => prompt.includes(x))!;
  const faithful = id === "thm_ok" || (id === "thm_fix" && prompt.includes("REFINED"));
  const issue = id === "thm_bad" ? "[missing-step] step 2 derives a bound the prose only names" : "[rendering] step 2 mismatch";
  return {
    stdout: JSON.stringify({ theorem: id, verdict: faithful ? "faithful" : "unfaithful", issues: faithful ? [] : [issue] }),
    stderr: "",
  };
};
// Stub renderer (the P2 repair hook): always produces the REFINED proof.
const stubRender = async (id: string) => proofBody(id, true);

let dir: string;

/** Write a layer as P1 does: formal_layer.json is the source of truth, formal_layer.tex its mirror. */
async function writeLayer(tex: string): Promise<void> {
  const blocks = parseAnchoredEnvs(tex).map((e) => ({ obj_id: e.obj_id, env: e.env, title: e.title, body: e.body.trim() }));
  await writeFile(join(dir, "formal_layer.json"), JSON.stringify({ blocks }), "utf8");
  await writeFile(join(dir, "formal_layer.tex"), tex, "utf8");
}

function makeIO(): StageIO {
  return {
    outDir: dir,
    ctx: {
      repoRoot: dir,
      qid: "q",
      spec: "v1",
      deps: { runCodex: stubRunCodex, runClaude: async () => "", dryRun: false },
    },
    bank: { leanSubdir: "Lean" },
    state: { notes: [] },
  } as unknown as StageIO;
}

const targets = [
  { obj_id: "thm_ok", isMain: true, lean: { file: "X.lean", decl: "thm_ok" } },
  { obj_id: "thm_fix", isMain: true, lean: { file: "X.lean", decl: "thm_fix" } },
  { obj_id: "thm_bad", isMain: false, lean: { file: "X.lean", decl: "thm_bad" } },
];

beforeEach(async () => {
  dir = await mkdtemp(join(tmpdir(), "proofaudit-"));
  await mkdir(join(dir, "proofs"), { recursive: true });
  await mkdir(join(dir, "Lean"), { recursive: true });
  await writeFile(join(dir, "Lean", "X.lean"), targets.map((t) => `theorem ${t.obj_id} : True := by\n  trivial`).join("\n\n"), "utf8");
  await writeFile(join(dir, "outline.md"), "# Title\n**Test.**\n\n# Notation\n- \\(x\\): a thing\n\n# Sections\n## section: Body\n", "utf8");
  await writeLayer(targets.map((t) => `\\begin{theoremv}{${t.obj_id}}\nStatement of ${t.obj_id}.\n\\end{theoremv}`).join("\n"));
  for (const t of targets) await writeFile(join(dir, "proofs", `${t.obj_id}.tex`), proofBody(t.obj_id) + "\n", "utf8");
});

afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("runProofAudit (P2 proof equivalence)", () => {
  it("returns a refined map for every proof and one problem for the residual-unfaithful proof", async () => {
    const { refined, problems } = await runProofAudit(makeIO(), targets, stubRender);

    // Every target appears in the refined map.
    expect([...refined.keys()].sort()).toEqual(["thm_bad", "thm_fix", "thm_ok"]);

    // Only thm_bad remains unfaithful → exactly one proof-audit problem, promotable (missing step).
    expect(problems).toHaveLength(1);
    expect(problems[0]).toMatchObject({ gate: "proof-audit", objId: "thm_bad", promotable: true });
    expect(problems[0].detail).toContain("thm_bad");
  });

  it("a rendering-only residual is NOT promotable, and a renderer that cannot improve stops the loop", async () => {
    let renders = 0;
    const render = async (id: string, prior: string) => { renders++; return id === "thm_bad" ? prior : proofBody(id, true); };
    const io = makeIO();
    (io.ctx.deps as { runCodex: unknown }).runCodex = async ({ prompt }: { prompt: string }) => {
      const r = await stubRunCodex({ prompt });
      return { ...r, stdout: r.stdout.replace("[missing-step]", "[rendering]") };
    };
    const { problems } = await runProofAudit(io, targets, render);
    expect(problems).toMatchObject([{ objId: "thm_bad", promotable: false }]);
    // thm_bad: one repair attempt returned the same proof → loop stopped (no second render).
    expect(renders).toBe(2); // thm_fix once, thm_bad once
  });

  it("leaves a faithful proof untouched and rewrites a refined one on disk", async () => {
    const { refined } = await runProofAudit(makeIO(), targets, stubRender);

    // thm_ok was faithful first pass → disk untouched; the returned map carries the
    // canonically-titled view (what P2 assembly uses).
    expect(refined.get("thm_ok")).toBe(canonicalizeProofTitle("thm_ok", proofBody("thm_ok")));
    expect(await readFile(join(dir, "proofs", "thm_ok.tex"), "utf8")).toBe(proofBody("thm_ok") + "\n");

    // thm_fix was refined → both the returned body and the persisted file carry the REFINED proof.
    expect(refined.get("thm_fix")).toBe(proofBody("thm_fix", true));
    expect(await readFile(join(dir, "proofs", "thm_fix.tex"), "utf8")).toBe(proofBody("thm_fix", true) + "\n");
  });

  it("persists the best attempt for the unfaithful proof and writes a drift report", async () => {
    await runProofAudit(makeIO(), targets, stubRender);
    // thm_bad's best (REFINED) attempt is persisted even though it never reconciled.
    expect(await readFile(join(dir, "proofs", "thm_bad.tex"), "utf8")).toBe(proofBody("thm_bad", true) + "\n");
    const drift = await readFile(join(dir, "logs", "graph_nl_drift.md"), "utf8");
    expect(drift).toContain("thm_bad (proof)");
  });

  it("records a faithful/unfaithful verdict cache and a review line per proof", async () => {
    await runProofAudit(makeIO(), targets, stubRender);
    const cache = JSON.parse(await readFile(join(dir, "proof_audit_cache.json"), "utf8"));
    expect(cache.thm_ok.verdict).toBe("faithful");
    const reviews = (await readFile(join(dir, "logs", "reviews.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    const refineLines = reviews.filter((r) => r.kind === "proof-refine");
    expect(refineLines.map((r) => r.obj_id).sort()).toEqual(["thm_bad", "thm_fix", "thm_ok"]);
  });
});

describe("proof-audit semantic notation fingerprint", () => {
  const row = (label: string, symbol: string, meaning: string, home: string) =>
    `| ${label} | ${symbol} | ${meaning} | ${home} |`;
  const table = (rows: string[]) => [
    "metadata: deliberately excluded from proof semantics",
    "| note symbol | paper notation | defining property in one phrase | home |",
    "|---|---|---|---|",
    ...rows,
  ].join("\n");
  const key = (notationTable: string) => proofAuditCacheKey({
    proofTex: "proof", leanPointer: "pointer", leanProofCacheSource: "source", notationTable, auditPromptFp: "fp", formalContext: "context",
  });

  it("is invariant to notation row order, home ownership, and non-table placement metadata", () => {
    const a = table([
      row("radius", "\\(w=A\\Delta^{1/q}\\)", "hypercube radius", "lem:old"),
      row("mass", "\\(m_n\\)", "common cell mass", "lem:packing"),
    ]);
    const b = table([
      row("mass", "\\(m_n\\)", "common cell mass", "thm:new-home"),
      row("radius", "\\(w=A\\Delta^{1/q}\\)", "hypercube radius", "thm:new-home"),
    ]).replace("metadata: deliberately excluded", "env_overrides: changed placement");
    expect(proofAuditSemanticNotation(a)).toBe(proofAuditSemanticNotation(b));
    expect(key(a)).toBe(key(b));
  });

  it("changes when exact symbol spelling or parameterization changes", () => {
    const base = table([row("radius", "\\(w=A\\Delta^{1/q}\\)", "hypercube radius", "lem:x")]);
    const spelling = table([row("radius", "\\(w_n=A\\Delta^{1/q}\\)", "hypercube radius", "lem:x")]);
    const parameters = table([row("radius", "\\(w=A\\Delta^{1/p}\\)", "hypercube radius", "lem:x")]);
    expect(key(spelling)).not.toBe(key(base));
    expect(key(parameters)).not.toBe(key(base));
  });

  it("changes when a symbol's reader-facing meaning changes", () => {
    const base = table([row("radius", "\\(w\\)", "hypercube radius", "lem:x")]);
    const changed = table([row("radius", "\\(w\\)", "cell probability", "lem:x")]);
    expect(key(changed)).not.toBe(key(base));
    expect(key(table([]))).not.toBe(key(base));
    expect(key(table([
      row("radius", "\\(w\\)", "hypercube radius", "lem:x"),
      row("mass", "\\(m\\)", "cell probability", "lem:x"),
    ]))).not.toBe(key(base));
  });

});

import { missingRealizedCitations } from "../src/presentation/audit.js";

describe("missingRealizedCitations (deterministic missing-citation check)", () => {
  const citables = [
    { objId: "lem:ambient-sample-marginal", decl: "CausalSmith.Stat.X.finProductLaw_eq_map" },
    { objId: "lem:pilot-sandwich", decl: "CausalSmith.Stat.X.pilot_sandwich" },
  ];

  it("flags a directly invoked realized decl the proof never crefs", () => {
    const lean = "theorem t : True := by\n  rw [productLaw, ← finProductLaw_eq_map (obsLaw P) n]\n  trivial";
    const tex = "\\begin{proof}[Proof of \\cref{obj:thm:t}] Direct argument. \\end{proof}";
    expect(missingRealizedCitations(lean, tex, citables, "thm:t")).toEqual([citables[0]]);
  });

  it("is satisfied by an existing \\cref and ignores the result's own env", () => {
    const lean = "theorem t := by exact finProductLaw_eq_map.trans (pilot_sandwich h)";
    const tex = "By \\cref{obj:lem:ambient-sample-marginal} and \\cref{obj:lem:pilot-sandwich}, done.";
    expect(missingRealizedCitations(lean, tex, citables, "thm:t")).toEqual([]);
    // A lemma auditing its own proof never demands a self-citation.
    expect(
      missingRealizedCitations("lemma l := finProductLaw_eq_map", "no crefs", citables, "lem:ambient-sample-marginal"),
    ).toEqual([]);
  });

  it("matches whole identifiers only, and stays silent without a Lean source", () => {
    // `finProductLaw_eq_map'` and `myfinProductLaw_eq_map` are different declarations.
    const lean = "theorem t := by exact finProductLaw_eq_map' (myfinProductLaw_eq_map h)";
    expect(missingRealizedCitations(lean, "no crefs", citables, "thm:t")).toEqual([]);
    expect(missingRealizedCitations("", "no crefs", citables, "thm:t")).toEqual([]);
  });
});

describe("proof-audit adjudication channel (flip verdict, keep key — the documented operator flow)", () => {
  // Integration regression for 32fe2964: the deterministic missing-citation hint used to
  // override a cached faithful verdict on EVERY hit, so the skill-documented adjudication
  // channel was silently defeated and the halt was unescapable (observed live 2026-08-26,
  // ~2.5h of cycles). Fixture: thm_adj's Lean proof invokes the citable lemma decl
  // `help_bound`; its paper proof does not cite \cref{obj:lem_help}, so the hint fires on
  // every pass.
  it("honors an adjudicated faithful verdict on an unchanged proof: no dispatch, hint suppressed with a note", async () => {
    await writeFile(
      join(dir, "Lean", "Y.lean"),
      ["theorem help_bound : True := by trivial", "", "theorem thm_adj : True := by", "  have h := help_bound", "  trivial", ""].join("\n"),
      "utf8",
    );
    const proofBody = "\\begin{proof}[Proof of \\cref{obj:thm_adj}]No citation here.\\end{proof}";
    await writeFile(join(dir, "proofs", "thm_adj.tex"), proofBody + "\n", "utf8");
    await writeFile(
      join(dir, "formal_layer.json"),
      JSON.stringify({
        blocks: [
          { obj_id: "thm_adj", env: "theoremv", title: null, body: "Target statement." },
          { obj_id: "lem_help", env: "lemmav", title: null, body: "Helper statement." },
        ],
      }),
      "utf8",
    );
    let codexCalls = 0;
    const countingCodex = async () => {
      codexCalls++;
      return { stdout: JSON.stringify({ theorem: "thm_adj", verdict: "unfaithful", issues: ["[rendering] codex disagrees"] }), stderr: "" };
    };
    const noRepair = async (_id: string, prior: string) => prior;
    const adjIO = () =>
      ({
        outDir: dir,
        ctx: { repoRoot: dir, qid: "q", spec: "v1", deps: { runCodex: countingCodex, runClaude: async () => "", dryRun: false } },
        bank: { leanSubdir: "Lean", graph: { nodes: [{ id: "lem_help", lean: { decl_name: "help_bound" } }] } },
        state: { notes: [] },
      }) as unknown as StageIO;
    const adjTargets = [{ obj_id: "thm_adj", isMain: true, lean: { file: "Y.lean", decl: "thm_adj" } }];

    // Pass 1: the judge says unfaithful and the renderer cannot improve → one problem, cached
    // judge verdict `unfaithful`.
    const r1 = await runProofAudit(adjIO(), adjTargets, noRepair);
    expect(r1.problems.length).toBeGreaterThan(0);
    const cachePath = join(dir, "proof_audit_cache.json");
    const cache = JSON.parse(await readFile(cachePath, "utf8"));
    expect(cache.thm_adj.verdict).toBe("unfaithful");
    expect(codexCalls).toBeGreaterThan(0);

    // Operator adjudication exactly as the skill prescribes: flip `verdict`, keep `key`.
    cache.thm_adj.verdict = "faithful";
    await writeFile(cachePath, JSON.stringify(cache), "utf8");

    // Pass 2, inputs unchanged: the key must be STABLE across runs, the hit must be honored
    // with ZERO model dispatches even though the missing-citation hint still fires, and the
    // suppression must be recorded — never silent.
    codexCalls = 0;
    const io2 = adjIO();
    const r2 = await runProofAudit(io2, adjTargets, noRepair);
    expect(r2.problems).toEqual([]);
    expect(codexCalls).toBe(0);
    expect((io2 as unknown as { state: { notes: string[] } }).state.notes.join("\n")).toMatch(
      /thm_adj.*missing-citation hint\(s\) noted on a judge-faithful proof/,
    );
  });
});

describe("proof audit — audit follow-ups", () => {
  it("retains earlier corrected findings when the next audit raises a different issue", async () => {
    const io = makeIO();
    const first = "[rendering] wrong tuning attribution";
    const second = "[rendering] wrong radius branch";
    let calls = 0;
    io.ctx.deps.runCodex = async () => ({
      stdout: JSON.stringify(++calls === 3 ? { verdict: "faithful", issues: [] } :
        { verdict: "unfaithful", issues: [calls === 1 ? first : second] }), stderr: "",
    });
    const received: { current: string[]; earlier: readonly string[] }[] = [];
    const result = await runProofAudit(io, [targets[1]], async (_id, prior, current, earlier) => {
      received.push({ current, earlier });
      return prior.replace("\\end{proof}", ` Fixed ${received.length}.\\end{proof}`);
    });
    expect(received).toEqual([
      { current: [first], earlier: [] },
      { current: [second], earlier: [first] },
    ]);
    expect(result.problems).toEqual([]);
    expect(calls).toBe(3);
    // The final candidate's current approval remains reusable without more repairs or judges.
    await runProofAudit(io, [targets[1]], async () => { throw new Error("already audited"); });
    expect(calls).toBe(3);
  });

  it.each(["unchanged", "null"])("reuses an exact %s repair failure across restarts and retries changed inputs", async (outcome) => {
    const io = makeIO();
    let judges = 0, renders = 0;
    io.ctx.deps.runCodex = async () => {
      judges++;
      return { stdout: JSON.stringify({ verdict: "unfaithful", issues: ["[rendering] wrong derivation"] }), stderr: "" };
    };
    const render = async (_id: string, prior: string) => { renders++; return outcome === "null" ? null : prior; };
    const context = new Map([[targets[2].obj_id, "render-context-v1"]]);
    const run = () => runProofAudit(io, [targets[2]], render, context);
    expect((await run()).problems).toHaveLength(1);
    expect((await run()).problems).toHaveLength(1);
    expect({ judges, renders }).toEqual({ judges: 1, renders: 1 });
    // Renderer-only changes (e.g. a corrected informal derivation) must release the failure.
    context.set(targets[2].obj_id, "render-context-v2");
    await run();
    expect({ judges, renders }).toEqual({ judges: 1, renders: 2 });
    // The same renderer inputs may face new judge issues under an operator correction.
    const cachePath = join(dir, "proof_audit_cache.json");
    const cache = JSON.parse(await readFile(cachePath, "utf8"));
    cache[targets[2].obj_id].issues = ["[rendering] corrected diagnosis"];
    await writeFile(cachePath, JSON.stringify(cache));
    await run();
    expect(renders).toBe(3);
    // Changed formal context requires a fresh judgement and repair, even for the same proof.
    await writeLayer("Changed target statements.");
    await run();
    expect({ judges, renders }).toEqual({ judges: 2, renders: 4 });
    await run();
    expect({ judges, renders }).toEqual({ judges: 2, renders: 4 });
  });

  it("keeps exhausted text-changing repairs stopped across restart and releases them on changed input", async () => {
    const io = makeIO();
    let judges = 0, renders = 0;
    io.ctx.deps.runCodex = async () => {
      judges++;
      return { stdout: JSON.stringify({ verdict: "unfaithful", issues: ["[rendering] unresolved derivation"] }), stderr: "" };
    };
    const render = async (_id: string, prior: string) => {
      renders++;
      return prior.replace("\\end{proof}", ` Attempt ${renders}.\\end{proof}`);
    };
    const context = new Map([[targets[2].obj_id, "render-context-v1"]]);
    const run = () => runProofAudit(io, [targets[2]], render, context);
    expect((await run()).problems).toHaveLength(1);
    expect({ judges, renders }).toEqual({ judges: 3, renders: 2 });
    expect((await run()).problems).toHaveLength(1);
    expect({ judges, renders }).toEqual({ judges: 3, renders: 2 });
    context.set(targets[2].obj_id, "render-context-v2");
    await run();
    expect({ judges, renders }).toEqual({ judges: 5, renders: 4 });
    await run();
    expect({ judges, renders }).toEqual({ judges: 5, renders: 4 });
    const proofPath = join(dir, "proofs", `${targets[2].obj_id}.tex`);
    await writeFile(proofPath, (await readFile(proofPath, "utf8")).replace("\\end{proof}", " Operator correction.\\end{proof}"));
    await run();
    expect({ judges, renders }).toEqual({ judges: 8, renders: 6 });
  });

  it("a repaired proof is cached under its OWN key: an unchanged re-run judges nothing", async () => {
    let judgeCalls = 0;
    const io = makeIO();
    const countingJudge = async (args: { prompt: string }) => { judgeCalls++; return stubRunCodex(args); };
    (io.ctx.deps as { runCodex: unknown }).runCodex = countingJudge;
    // The repair mentions a symbol the draft did not, so the per-proof notation slice differs.
    await writeFile(join(dir, "outline.md"), "# Title\n**T.**\n\n# Notation\n\\(\\alpha\\) | \\(\\alpha\\) | rate | thm_fix\n\\(\\beta\\) | \\(\\beta\\) | width | thm_fix\n\n# Sections\n## section: Body\n", "utf8");
    const render = async (id: string) => `\\begin{proof}[Proof of \\cref{obj:${id}}]REFINED proof of ${id} with \\(\\beta\\)\\end{proof}`;
    await runProofAudit(io, [targets[1]], render);
    expect(judgeCalls).toBe(2); // draft (unfaithful) + repaired (faithful)
    judgeCalls = 0;
    const io2 = makeIO();
    (io2.ctx.deps as { runCodex: unknown }).runCodex = countingJudge;
    const { problems } = await runProofAudit(io2, [targets[1]], render);
    expect(problems).toEqual([]);
    expect(judgeCalls).toBe(0);
  });

  it("a missing-citation hint on a judge-FAITHFUL proof is advisory on the first run too (no halt, note recorded)", async () => {
    await writeFile(join(dir, "Lean", "Y.lean"), ["theorem help_bound : True := by trivial", "theorem thm_hint : True := by\n  have h := help_bound\n  trivial"].join("\n\n"), "utf8");
    await writeFile(join(dir, "proofs", "thm_hint.tex"), "\\begin{proof}[Proof of \\cref{obj:thm_hint}]No citation.\\end{proof}\n", "utf8");
    await writeFile(join(dir, "formal_layer.json"), JSON.stringify({ blocks: [
      { obj_id: "thm_hint", env: "theoremv", title: null, body: "T." },
      { obj_id: "lem_help", env: "lemmav", title: null, body: "H." },
    ] }), "utf8");
    let renders = 0;
    const io = {
      outDir: dir,
      ctx: { repoRoot: dir, qid: "q", spec: "v1", deps: { runCodex: async () => ({ stdout: JSON.stringify({ theorem: "thm_hint", verdict: "faithful", issues: [] }), stderr: "" }), runClaude: async () => "", dryRun: false } },
      bank: { leanSubdir: "Lean", graph: { nodes: [{ id: "lem_help", lean: { decl_name: "help_bound" } }] } },
      state: { notes: [] as string[] },
    } as unknown as StageIO;
    const { problems } = await runProofAudit(io, [{ obj_id: "thm_hint", isMain: true, lean: { file: "Y.lean", decl: "thm_hint" } }], async (_id, prior) => { renders++; return prior; });
    expect(problems).toEqual([]);
    expect(renders).toBe(0);
    expect((io as unknown as { state: { notes: string[] } }).state.notes.join("\n")).toMatch(/thm_hint.*missing-citation hint\(s\) noted on a judge-faithful proof/);
  });

  it("a cached unfaithful verdict without issues is re-judged rather than repaired against nothing", async () => {
    await writeFile(join(dir, "proof_audit_cache.json"), JSON.stringify({ thm_ok: { key: "stale", verdict: "unfaithful" } }), "utf8");
    let judgeCalls = 0;
    const io = makeIO();
    (io.ctx.deps as { runCodex: unknown }).runCodex = async (args: { prompt: string }) => { judgeCalls++; return stubRunCodex(args); };
    const { problems } = await runProofAudit(io, [targets[0]], async (_id, prior) => prior);
    expect(problems).toEqual([]);
    expect(judgeCalls).toBe(1);
  });
});


describe("proof audit recovery and context", () => {
  it("supplies exact current statements and source lookup guidance without rereading the target", async () => {
    await writeLayer(String.raw`\begin{theoremv}{thm_ok}
The exact target statement uses \cref{obj:helper}.
\end{theoremv}
\begin{lemmav}{helper}
A necessary helper statement.
\end{lemmav}
\begin{lemmav}{other}
An unrelated statement body.
\end{lemmav}`);
    const io = makeIO();
    let calls = 0;
    io.ctx.deps.runCodex = async ({ prompt }) => {
      calls++;
      expect(prompt).toContain("The exact target statement");
      expect(prompt).not.toContain("A necessary helper statement."); // cited by the statement, not by the proof
      expect(prompt).not.toContain("An unrelated statement body.");
      expect(prompt).toContain("The exact declaration is supplied below");
      expect(prompt).not.toContain("Read the file with your tools; do not guess its contents.");
      return { stdout: JSON.stringify({ verdict: "faithful", issues: [] }), stderr: "" };
    };
    await runProofAudit(io, [targets[0]], stubRender);
    await runProofAudit(io, [targets[0]], stubRender);
    expect(calls).toBe(1);
  });

  const LAYER = String.raw`\begin{definitionv}{def:a}[Object A]
Let \(A\) be the object.
\end{definitionv}
\begin{definitionv}{def:psi}[The functional \(\Psi\)]
Let \(\Psi(h) = \int h\, w_{\mathrm{clip}}\).
\end{definitionv}
\begin{definitionv}{def:zeta}[The functional \(\zeta\)]
Let \(\zeta(h) = \sup h\).
\end{definitionv}
\begin{definitionv}{def:w}[Clipped weight]
The clipped weight is \(w_{\mathrm{clip}}(x) = \min\{w(x), M\}\), which is nonnegative.
\end{definitionv}
\begin{definitionv}{def:phi}
The body-only functional is \(\Phi(h) = \int h\, w_{\mathrm{clip}}\).
\end{definitionv}
\begin{definitionv}{def:prose}
We say a design is admissible when every arm is sampled.
\end{definitionv}
\begin{assumptionv}{ass:unused}
An assumption no statement in the closure cites.
\end{assumptionv}
\begin{theoremv}{thm_ok}
The exact target statement on \(\Psi(A)\) uses \cref{obj:helper}.
\end{theoremv}
\begin{lemmav}{helper}
A necessary helper statement.
\end{lemmav}
\begin{lemmav}{other}
An unrelated statement body.
\end{lemmav}`;

  it("keys approval on the proof's own statements only: the target and what the proof cites", async () => {
    await writeLayer(LAYER);
    await writeFile(join(dir, "proofs", "thm_ok.tex"), "\\begin{proof}[Proof of \\cref{obj:thm_ok}]By \\cref{obj:helper}.\\end{proof}\n");
    let calls = 0;
    const io = makeIO();
    io.ctx.deps.runCodex = async (args) => { calls++; return stubRunCodex(args); };
    await runProofAudit(io, [targets[0]], stubRender);
    expect(calls).toBe(1);
    // Reordering the layer, re-rendering an uncited lemma, promoting a helper, or changing ANY
    // definition or assumption the proof does not cite keeps the approval: the audit judges the
    // translation of the Lean proof, and those are their own statements' P1 concern.
    const envs = parseAnchoredEnvs(LAYER);
    const block = (e: (typeof envs)[number]) => `\\begin{${e.env}}{${e.obj_id}}${e.title ? `[${e.title}]` : ""}\n${e.body.trim()}\n\\end{${e.env}}`;
    for (const layer of [
      [...envs].reverse().map(block).join("\n"),
      LAYER.replace("An unrelated statement body.", "A re-rendered unrelated body."),
      `${LAYER}\n\\begin{lemmav}{lem:promoted}\nA promoted helper.\n\\end{lemmav}`,
      LAYER.replace("Let \\(A\\) be the object.", "Let \\(A\\) be a different object."),
      LAYER.replace("Let \\(\\Psi(h) = \\int h\\, w_{\\mathrm{clip}}\\).", "Let \\(\\Psi(h) = 2\\int h\\)."),
      LAYER.replace("which is nonnegative", "which may be negative"),
      LAYER.replace("when every arm is sampled", "when every arm is sampled twice"),
      LAYER.replace("An assumption no statement", "A CHANGED assumption no statement"),
    ]) {
      await writeLayer(layer);
      await runProofAudit(io, [targets[0]], stubRender);
    }
    expect(calls).toBe(1);
    // A cited statement or the target statement changing does invalidate it.
    await writeLayer(LAYER.replace("A necessary helper statement.", "A CHANGED helper statement."));
    await runProofAudit(io, [targets[0]], stubRender);
    expect(calls).toBe(2);
    await writeLayer(LAYER.replace("The exact target statement", "The CHANGED target statement"));
    await runProofAudit(io, [targets[0]], stubRender);
    expect(calls).toBe(3);
  });

  it("proofAuditFormalContext: order-independent; the target and the proof's own citations, one hop", () => {
    const envs = parseAnchoredEnvs(LAYER);
    const proof = (text: string) => `\\begin{proof}[Proof of \\cref{obj:thm_ok}]${text}\\end{proof}`;
    const ctx = proofAuditFormalContext(envs, "thm_ok", proof("Immediate."));
    expect(ctx.split("\n").map((l) => l.split("|")[0])).toEqual(["thm_ok"]); // helper is cited by the statement, not the proof
    expect(proofAuditFormalContext([...envs].reverse(), "thm_ok", proof("Immediate."))).toBe(ctx);
    const cited = proofAuditFormalContext(envs, "thm_ok", proof("By \\cref{obj:helper} and \\Cref{obj:def:w}. % \\cref{obj:other} in a comment does not count"));
    expect(cited.split("\n").map((l) => l.split("|")[0])).toEqual(["def:w", "helper", "thm_ok"]);
    expect(cited).not.toContain("other|");
  });

  it("judges against formal_layer.json even when the derived formal_layer.tex is stale", async () => {
    await writeLayer(LAYER);
    await writeFile(join(dir, "formal_layer.tex"), LAYER.replace("The exact target statement", "A STALE derived statement"), "utf8");
    const io = makeIO();
    let prompt = "";
    io.ctx.deps.runCodex = async (args) => { prompt = args.prompt; return stubRunCodex(args); };
    await runProofAudit(io, [targets[0]], stubRender);
    expect(prompt).toContain("The exact target statement");
    expect(prompt).not.toContain("A STALE derived statement");
  });

  it("retries a judge reply with no usable verdict once, then throws — never a writer round", async () => {
    let judges = 0, renders = 0;
    const io = makeIO();
    io.ctx.deps.runCodex = async () => { judges++; return { stdout: judges === 1 ? "I cannot decide." : JSON.stringify({ verdict: "faithful", issues: [] }), stderr: "" }; };
    const render = async (_id: string, prior: string) => { renders++; return prior; };
    expect((await runProofAudit(io, [targets[0]], render)).problems).toEqual([]);
    expect({ judges, renders }).toEqual({ judges: 2, renders: 0 });
    judges = 0;
    io.ctx.deps.runCodex = async () => { judges++; return { stdout: JSON.stringify({ verdict: "unfaithful", issues: [] }), stderr: "" }; };
    await expect(runProofAudit(io, [targets[1]], render)).rejects.toThrow(/no usable verdict/);
    expect({ judges, renders }).toEqual({ judges: 2, renders: 0 });
  });

  it("supplies the helper declarations the Lean proof names, so the judge need not read files", async () => {
    await writeFile(join(dir, "Lean", "H.lean"), "theorem helper_fact : True := by\n  trivial\n", "utf8");
    await writeFile(join(dir, "Lean", "X.lean"), targets.map((t) => `theorem ${t.obj_id} : True := by\n  exact helper_fact`).join("\n\n"), "utf8");
    await writeLayer(LAYER);
    const io = makeIO();
    let prompt = "";
    io.ctx.deps.runCodex = async (args) => { prompt = args.prompt; return { stdout: JSON.stringify({ verdict: "faithful", issues: [] }), stderr: "" }; };
    await runProofAudit(io, [targets[0]], stubRender);
    expect(prompt).toContain("HELPER DECLARATIONS");
    expect(prompt).toContain("-- helper_fact  (H.lean)\ntheorem helper_fact : True := by\n  trivial");
    expect(prompt).toContain("no file read is needed for them");
    expect(prompt).not.toContain("For helper searches, start in the named source directory");
  });

  it("honours a verdict row stamped under the prompt fingerprint before deterministic context was added", async () => {
    await writeLayer(LAYER);
    const { LEGACY_PROOF_AUDIT_PROMPT_FPS, proofAuditCacheKey, proofAuditFormalContext } = await import("../src/presentation/audit.js");
    const proofTex = canonicalizeProofTitle("thm_ok", (await readFile(join(dir, "proofs", "thm_ok.tex"), "utf8")).trim());
    const source = await readFile(join(dir, "Lean", "X.lean"), "utf8");
    const { extractFullDeclSource } = await import("../src/presentation/lean_extract.js");
    const envs = parseAnchoredEnvs(LAYER);
    const oldKey = proofAuditCacheKey({
      proofTex, leanPointer: "Lean/X.lean:thm_ok", leanProofCacheSource: extractFullDeclSource(source, "thm_ok", 1),
      notationTable: "(no artifact-specific notation rows)", auditPromptFp: LEGACY_PROOF_AUDIT_PROMPT_FPS[0],
      formalContext: proofAuditFormalContext(envs, "thm_ok", proofTex),
    });
    await writeFile(join(dir, "proof_audit_cache.json"), JSON.stringify({ thm_ok: { key: oldKey, verdict: "faithful", issues: [] } }));
    const io = makeIO();
    io.ctx.deps.runCodex = async () => { throw new Error("an approval under the previous prompt must be reused"); };
    expect((await runProofAudit(io, [targets[0]], stubRender)).problems).toEqual([]);
    const cache = JSON.parse(await readFile(join(dir, "proof_audit_cache.json"), "utf8"));
    expect(cache.thm_ok.key).not.toBe(oldKey);
    expect(cache.thm_ok.verdict).toBe("faithful");
  });

  it("honours a verdict row stamped under the pre-closure key and re-stamps it without a judge call", async () => {
    await writeLayer(LAYER);
    const proofTex = (await readFile(join(dir, "proofs", "thm_ok.tex"), "utf8")).trim();
    const source = await readFile(join(dir, "Lean", "X.lean"), "utf8");
    const { extractFullDeclSource } = await import("../src/presentation/lean_extract.js");
    const leanSource = extractFullDeclSource(source, "thm_ok", 1);
    const legacyKey = hashEnvBody([
      PRESENTATION_PROSE_POLICY_VERSION, await promptFingerprint("proof_audit"), hashEnvBody(LAYER),
      parseAnchoredEnvs(LAYER).find((e) => e.obj_id === "thm_ok")!.body.trim(), canonicalizeProofTitle("thm_ok", proofTex),
      `file: ${join(dir, "Lean", "X.lean")}\ndeclaration: thm_ok\nRead the file with your tools; do not guess its contents.`,
      leanSource, proofAuditSemanticNotation("(no artifact-specific notation rows)"),
    ].join("|"));
    await writeFile(join(dir, "proof_audit_cache.json"), JSON.stringify({ thm_ok: { key: legacyKey, verdict: "faithful", issues: [] } }));
    const io = makeIO();
    io.ctx.deps.runCodex = async () => { throw new Error("a legacy-keyed approval must be reused"); };
    expect((await runProofAudit(io, [targets[0]], stubRender)).problems).toEqual([]);
    const cache = JSON.parse(await readFile(join(dir, "proof_audit_cache.json"), "utf8"));
    expect(cache.thm_ok.key).not.toBe(legacyKey);
    expect((await runProofAudit(io, [targets[0]], stubRender)).problems).toEqual([]);
  });

  it("repairs a dropped kind prefix in place and routes an unresolvable \\cref to the writer before any judge call", async () => {
    await writeLayer(LAYER.replace("{helper}", "{lem:helper}"));
    await writeFile(join(dir, "proofs", "thm_ok.tex"), "\\begin{proof}[Proof of \\cref{obj:thm_ok}]By \\cref{obj:helper} and \\cref{obj:synth_99}.\\end{proof}\n");
    let judges = 0;
    const issuesSeen: string[][] = [];
    const io = makeIO();
    io.ctx.deps.runCodex = async (args) => { judges++; return stubRunCodex(args); };
    const render = async (_id: string, prior: string, issues: string[]) => {
      issuesSeen.push(issues);
      return prior.replace(" and \\cref{obj:synth_99}", "");
    };
    const { refined, problems } = await runProofAudit(io, [targets[0]], render, new Map([["thm_ok", "ctx"]]));
    expect(problems).toEqual([]);
    expect(issuesSeen).toHaveLength(1);
    expect(issuesSeen[0][0]).toMatch(/^\[rendering\] .*obj:synth_99/);
    expect(issuesSeen[0].some((i) => i.includes("obj:helper"))).toBe(false); // the prefix drop was repaired, not reported
    expect(refined.get("thm_ok")).toContain("\\cref{obj:lem:helper}");
    expect(refined.get("thm_ok")).not.toContain("synth_99");
    expect(judges).toBe(1); // the judge saw only the resolved proof
    expect(await readFile(join(dir, "proofs", "thm_ok.tex"), "utf8")).toContain("obj:lem:helper");
  });

  it("halts on a reference the writer cannot resolve, without a judge call, and stays stopped on unchanged re-entry", async () => {
    await writeLayer(LAYER);
    await writeFile(join(dir, "proofs", "thm_ok.tex"), "\\begin{proof}[Proof of \\cref{obj:thm_ok}]By \\cref{obj:nowhere}.\\end{proof}\n");
    let judges = 0, renders = 0;
    const io = makeIO();
    io.ctx.deps.runCodex = async () => { judges++; throw new Error("no judge call expected"); };
    const render = async (_id: string, prior: string) => { renders++; return prior; };
    const context = new Map([["thm_ok", "ctx"]]);
    const first = await runProofAudit(io, [targets[0]], render, context);
    expect(first.problems).toMatchObject([{ objId: "thm_ok", promotable: false }]);
    expect(first.problems[0].issues[0]).toContain("obj:nowhere");
    expect({ judges, renders }).toEqual({ judges: 0, renders: 1 });
    await runProofAudit(io, [targets[0]], render, context);
    expect({ judges, renders }).toEqual({ judges: 0, renders: 1 });
  });

  it("fails before dispatch when the formal context is missing", async () => {
    await rm(join(dir, "formal_layer.json"));
    let calls = 0;
    const io = makeIO();
    io.ctx.deps.runCodex = async (args) => { calls++; return stubRunCodex(args); };
    await expect(runProofAudit(io, [targets[0]], stubRender)).rejects.toThrow();
    expect(calls).toBe(0);
  });

  it("persists a repaired candidate even when its next judge call fails", async () => {
    const io = makeIO();
    io.ctx.deps.runCodex = async (args) => {
      if (args.prompt.includes("REFINED")) throw new Error("judge unavailable");
      return stubRunCodex(args);
    };
    await expect(runProofAudit(io, [targets[1]], stubRender)).rejects.toThrow("judge unavailable");
    const candidate = await existingProofForP2(join(dir, "proofs", "thm_fix.tex"), "old-context", "new-context");
    expect(candidate?.text).toContain("REFINED");
    expect(candidate?.cacheHit).toBe(false);
    let renders = 0;
    const resumed = await runProofAudit(makeIO(), [targets[1]], async () => { renders++; return null; });
    expect(resumed.problems).toEqual([]);
    expect(renders).toBe(0);
  });

  it("drains a successful sibling and retains its approval when another worker fails", async () => {
    let release!: () => void;
    const failed = new Promise<void>((resolve) => { release = resolve; });
    const io = makeIO();
    io.ctx.deps.runCodex = async (args) => {
      if (args.prompt.includes('"theorem": "thm_bad"')) { release(); throw new Error("sibling failed"); }
      await failed;
      return stubRunCodex(args);
    };
    await expect(runProofAudit(io, [targets[1], targets[2]], stubRender)).rejects.toThrow("sibling failed");
    expect(await readFile(join(dir, "proofs", "thm_fix.tex"), "utf8")).toContain("REFINED");
    const cache = JSON.parse(await readFile(join(dir, "proof_audit_cache.json"), "utf8"));
    expect(cache.thm_fix.verdict).toBe("faithful");
    const resumeIO = makeIO();
    resumeIO.ctx.deps.runCodex = async () => { throw new Error("should reuse completed approval"); };
    expect((await runProofAudit(resumeIO, [targets[1]], stubRender)).problems).toEqual([]);
  });
});
