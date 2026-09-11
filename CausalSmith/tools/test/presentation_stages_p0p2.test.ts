import { describe, it, expect, beforeAll, afterAll, vi } from "vitest";
import { appendFile, readFile, rm, mkdtemp, writeFile, cp, readdir } from "node:fs/promises";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { runPaperPipeline, type PaperDeps } from "../src/presentation/pipeline.js";
import { parseAnchoredEnvs, lintAnchors, type AnchoredEnv } from "../src/presentation/tex_anchors.js";
import { FormalLayerSource } from "../src/presentation/formal_layer.js";
import { parseBib } from "../src/presentation/citations.js";
import { parseNotationReviewerOutput } from "../src/presentation/stages/p1_plan.js";
import { acceptedBankEntry, causalSmithRoot } from "./helpers.js";
import { graphPath, saveGraph } from "../src/graph/store.js";
import { loadBankEntry } from "../src/presentation/bank.js";
import { proofFileName, proofObjId } from "../src/presentation/proof_files.js";
import { parseOutline } from "../src/presentation/stage_util.js";
import { rewriteOutlineObjs } from "../src/presentation/p1_order.js";
import { MODELS } from "../src/models.js";
import { applyProseRevision, proofBlocks, applyTargetedReplacements } from "../src/presentation/prose_revision.js";
import { citedScopeFootnote } from "../src/presentation/formal_layer.js";

// Read real Lean sources, but freeze stub bodies only into a disposable bank copy.
const isolatedBank = vi.hoisted(() => ({ dir: "" }));
vi.mock("../src/presentation/paths.js", async (importOriginal) => {
  const original = await importOriginal<typeof import("../src/presentation/paths.js")>();
  return { ...original, bankAcceptedDir: (...args: Parameters<typeof original.bankAcceptedDir>) =>
    isolatedBank.dir || original.bankAcceptedDir(...args) };
});

// Run against whatever paper is currently banked (the pipeline reads its graph + Lean; the models
// are stubbed). Tracks bank re-curation instead of a hardcoded qid.
const { qid: QID, spec: SPEC } = acceptedBankEntry();

/** Copy the fixture entry into an isolated bank. The fixture is whichever accepted entry sorts
 *  first; one that has already been presented carries frozen bodies, which P1 reuses instead of
 *  rendering — strip them so the render paths under test (batch touch-up, omission recovery) run. */
async function copyBankFixture(dest: string): Promise<void> {
  await cp(join(causalSmithRoot(), "doc", "research", "_bank", "accepted", `${QID}_${SPEC}`), dest, { recursive: true });
  const graphPath = join(dest, "graph.json");
  const graph = JSON.parse(await readFile(graphPath, "utf8"));
  for (const node of graph.nodes ?? []) if (node.nl && "frozen_body" in node.nl) delete node.nl.frozen_body;
  await writeFile(graphPath, JSON.stringify(graph, null, 2) + "\n", "utf8");
}

const BIB = `@article{robins1994,
  title = {Estimation of Regression Coefficients When Some Regressors Are Not Always Observed},
  author = {Robins, James M. and Rotnitzky, Andrea and Zhao, Lue Ping},
  journal = {Journal of the American Statistical Association}, year = {1994},
  doi = {10.1080/01621459.1994.10476818}
}`;

const renderEnv = (e: AnchoredEnv) =>
  `\\begin{${e.env}}{${e.obj_id}}${e.title !== null ? `[${e.title}]` : ""}\n${e.body.trim()}\n\\end{${e.env}}`;

// The P1 outline is now a codex (executor) call; build it from the mechanical
// layer's node-id envs in the prompt.
const stubOutline = (prompt: string): string => {
  const envs = parseAnchoredEnvs(prompt);
  const by = (k: AnchoredEnv["env"][]) =>
    envs.filter((e) => k.includes(e.env)).map((e) => e.obj_id).join(", ");
  const propositionFixture = envs.find((e) => e.env === "theoremv")?.obj_id;
  if (!propositionFixture) throw new Error("P0-P2 fixture requires a theorem to override as propositionv");
  return [
    "# Title",
    "Stub Paper Title",
    `env_overrides: ${propositionFixture}=propositionv`,
    "# Notation",
    "| `τ` | tau | the ATE |",
    "# Sections",
    "## section: Introduction",
    "intro brief",
    "objs: none",
    "bib: robins1994",
    "## section: Setup and assumptions",
    "setup brief",
    `objs: ${by(["assumptionv", "definitionv"])}`,
    "bib: robins1994",
    "## section: Main results",
    "results brief",
    `objs: ${by(["theoremv", "propositionv"])}`,
    "bib: robins1994",
    "## section: Auxiliary lemmas",
    "lemma brief",
    `objs: ${by(["lemmav"])}`,
    "bib: robins1994",
  ].join("\n");
};

const STUB_BODY = "Touched statement body.";
let outlineAttempts = 0;
let batchOmissionExercised = false;
let omittedBatchId = "";
let singleRecoveryCalls = 0;
// One entry per proof-render prompt: true iff a REAL D-stage
// derivation (not the "(none recorded…)" placeholder) reached the prompt.
const derivationSeen: boolean[] = [];

const mainProofCitableSets: { target: string; targetEnv: string; seen: string[]; catalog: string[]; exactLean: boolean; targetedLookup: boolean }[] = [];
// Section prompts carrying REAL D-stage per-result notes / front matter carrying the
// REAL contribution narrative (not the "(none recorded)" placeholder).
const sectionNotesSeen: boolean[] = [];
let frontNarrativeSeen = false;
let p0Model = "";
let p0Effort = "";
let frontMatterPrompt = "";
let frontMatterCalls = 0;
let sectionDraftCalls = 0;
let sectionReferenceNormalizationTarget = "";

// The P1 loop's cross-reference gate requires each statement to \cref every dependency in its ref_set,
// and the hypothesis-presentation gate requires a theorem/lemma with ≥4 hypotheses to itemize them.
// A real render writes both; the stub must too, or the loop never converges. So the stub emits one
// \item per ref_set dependency (a target-typed \cref) — satisfying both gates uniformly.
const parseRefs = (csv: string): string[] =>
  csv.split(",").map((s) => s.trim()).filter((s) => s && s !== "(none)");
const stubEnv = (id: string, refIds: string[]): string => {
  const items = refIds.length
    ? `\n\\begin{itemize}\n${refIds.map((r) => `\\item \\cref{obj:${r}}`).join("\n")}\n\\end{itemize}`
    : "";
  return `@@@ENV ${id}@@@\nTITLE: Stub Title\n@@@BODY@@@\n${STUB_BODY}${items}\n@@@END@@@`;
};

const deps: PaperDeps = {
  // P0–P2 drive every model call through codex; runClaude (the P3 rubric ensemble) is never reached.
  runClaude: async () => "STUB",
  runCodex: async ({ prompt, model, reasoningEffort }) => {
    // P0 literature pool (now codex via hosted web_search).
    if (prompt.includes("=== PROMPT: p0_literature ===")) {
      p0Model = model ?? "";
      p0Effort = reasoningEffort ?? "";
      return {
        stdout: "```bibtex\n" + BIB + "\n```\n```markdown\nRelated-work brief stub.\n```\n",
        stderr: "",
      };
    }
    // P1 outline (executor / codex).
    if (prompt.includes("=== PROMPT: p1_plan ===")) {
      outlineAttempts += 1;
      const outline = stubOutline(prompt);
      // Exercise the bounded repair path: the first draft violates the verified-pool
      // contract, while the replacement prompted with validator feedback is clean.
      return {
        stdout: outlineAttempts === 1 ? outline.replace("bib: robins1994", "bib: dropped2006") : outline,
        stderr: "",
      };
    }
    // P1 Lean-aware render: one theorem/lemma statement from its Lean signature (same @@@ENV envelope).
    if (prompt.includes("Render ONE formal statement")) {
      const id = prompt.match(/^Object:\s*(\S+)\s+\(kind:/m)?.[1] ?? "unknown";
      const refs = parseRefs(prompt.match(/Dependencies you may[^\n]*\n([^\n]*)/)?.[1] ?? "");
      return { stdout: stubEnv(id, refs), stderr: "" };
    }
    // P1 touch-up render (delimiter format): STUB_BODY + the env's ref_set refs, per ### <id> block.
    if (prompt.includes("Render each formal environment")) {
      const blocks = prompt.split(/^### /m).slice(1);
      let out = blocks.map((blk) => {
        const id = blk.split(/\n/)[0].trim();
        const refs = parseRefs(blk.match(/ref_set:\s*(.+)/)?.[1] ?? "");
        return stubEnv(id, refs);
      });
      if (blocks.length > 1 && !batchOmissionExercised) {
        batchOmissionExercised = true;
        omittedBatchId = blocks[0].split(/\n/)[0].trim();
        out = out.slice(1);
      } else if (blocks.length === 1 && blocks[0].split(/\n/)[0].trim() === omittedBatchId) {
        singleRecoveryCalls += 1;
      }
      return { stdout: out.join("\n\n"), stderr: "" };
    }
    // P1 notation-resolvability review (now codex) → clean.
    if (prompt.includes("NOTATION-RESOLVABILITY")) {
      return { stdout: JSON.stringify({ problems: [] }), stderr: "" };
    }
    // P1 statement equivalence audit (runStatementAudit). Batch: faithful for each `--- <id> ---`.
    if (prompt.includes("statement-faithfulness auditor")) {
      if (prompt.includes("For EACH statement below")) {
        const ids = [...prompt.matchAll(/^--- (\S+) ---$/gm)].map((m) => m[1]);
        return { stdout: JSON.stringify({ results: ids.map((id) => ({ obj_id: id, verdict: "faithful" })) }), stderr: "" };
      }
      return { stdout: JSON.stringify({ verdict: "faithful" }), stderr: "" };
    }
    // P2 proof equivalence audit (runProofAudit) → faithful.
    if (prompt.includes("auditing whether a prose appendix proof faithfully")) {
      return { stdout: JSON.stringify({ verdict: "faithful" }), stderr: "" };
    }
    // P2 body section (now codex).
    if (prompt.includes("Write ONE section")) {
      if (prompt.includes("Per-result notes from the research stage")) {
        sectionNotesSeen.push(!prompt.includes("{{result_notes}}") && !/Per-result notes[^\n]*\n[^\n]*\(none recorded\)/.test(prompt));
      }
      // Only the section's own environments: the prompt also carries the sections already
      // drafted, whose environments a real drafter must not reproduce.
      const own = prompt.slice(prompt.indexOf("Formal environments that belong in this section"), prompt.indexOf("Sections already drafted"));
      const envs = parseAnchoredEnvs(own);
      sectionDraftCalls += 1;
      const prose = sectionReferenceNormalizationTarget
        ? `Prose stub \\(\\cref{obj:${sectionReferenceNormalizationTarget}}\\).`
        : "Prose stub.";
      return {
        stdout: "\\section{Stub Section}\n" + prose + "\n\n" + envs.map(renderEnv).join("\n\n"),
        stderr: "",
      };
    }
    // P2 intro + abstract (now codex).
    if (prompt.includes("abstract and introduction")) {
      frontNarrativeSeen =
        prompt.includes("Contribution narrative from the research stage") &&
        !prompt.includes("{{contribution_narrative}}") &&
        prompt.includes("TLDR (pre-formalization research summary)");
      frontMatterPrompt = prompt;
      frontMatterCalls += 1;
      return {
        stdout:
          "\\begin{abstract}\nStub abstract.\n\\end{abstract}\n\\section{Introduction}\nStub intro \\citep{robins1994}.",
        stderr: "",
      };
    }
    // Single main-result proof render (p2_proof). The stub must reproduce the prompt's REQUIRED
    // title, `\begin{proof}[Proof of \cref{obj:<id>}]` — with a generic "[Proof]" the assembled
    // paper carries no way to tell which result a proof belongs to, and the proof-dropped lint
    // (rightly) reports every main result as unproved.
    const mainEnv = prompt.match(/\\begin\{(theoremv|propositionv|lemmav)\}\{([\w:-]+)\}/);
    const thmId = mainEnv?.[2];
    if (thmId) {
      const catalog = [...prompt.matchAll(/^([A-Za-z0-9:_-]+) \| /gm)].map(m => m[1]);
      mainProofCitableSets.push({ target: thmId, targetEnv: mainEnv![1], catalog,
        exactLean: /Lean proof source:[\s\S]*?\b(?:theorem|lemma|def)\s/.test(prompt),
        targetedLookup: prompt.includes("formal_layer.json") && prompt.includes("retrieve only that object by obj_id"), seen:
        [...prompt.matchAll(/\\begin\{(?:lemmav|theoremv|propositionv)\}\{([\w:-]+)\}/g)].map((m) => m[1]),
      });
      if (prompt.includes("Informal derivation from the discovery stage")) {
        derivationSeen.push(
          !prompt.includes("(none recorded for this result)") && !prompt.includes("{{informal_derivation}}"),
        );
      }
      // The prompt carries the paper's citable envs; cite them, as a real proof does. Without
      // this the assembled paper has lemmas no proof uses (isolated-lemma gate), and a proof
      // whose Lean route invokes another result env's decl without a \cref trips the
      // deterministic missing-citation check — both gates rightly reject the stub otherwise.
      const helperIds = [...new Set(
        [...prompt.matchAll(/\\begin\{(?:lemmav|theoremv|propositionv)\}\{([\w:-]+)\}/g)].map((m) => m[1]).concat(catalog),
      )].filter((id) => id !== thmId);
      const cite = helperIds.length > 0 ? ` By \\cref{${helperIds.map((id) => `obj:${id}`).join(",")}}.` : "";
      return {
        stdout: `chatter\n\\begin{proof}[Proof of \\cref{obj:${thmId}}]\nStep 1.${cite} % lean: t_thm\n\\end{proof}\nmore chatter`,
        stderr: "",
      };
    }
    return {
      stdout: "chatter\n\\begin{proof}[Proof]\nStep 1. % lean: t_thm\n\\end{proof}\nmore chatter",
      stderr: "",
    };
  },
  lookup: async (e) =>
    e.key === "robins1994"
      ? {
          title:
            "Estimation of regression coefficients when some regressors are not always observed",
          authorFamily: "Robins",
          year: 1994,
        }
      : null,
  dryRun: false,
};

// Integration against the real bank entry (real Lean tree, Mathlib lookups): well over the
// default 5 s budget when the whole suite runs in parallel.
vi.setConfig({ testTimeout: 60_000 });

describe("stages P0-P2 against the real bank entry (stubbed models)", () => {
  const root = causalSmithRoot();
  // NEVER the real presentationDir: a test run must not clobber live artifacts.
  const dirP = mkdtemp(join(tmpdir(), "causalsmith-p0p2-"));
  afterAll(async () => rm(await dirP, { recursive: true, force: true }));
  beforeAll(async () => {
    isolatedBank.dir = join(await dirP, "bank");
    await copyBankFixture(isolatedBank.dir);
  });

  it("P0+P1 produce pool, outline, frozen layer; halts at outline checkpoint", async () => {
    const dir = await dirP;
    const r = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, outDir: dir });
    expect(r.halt).toBe("checkpoint:outline");
    expect(p0Model).toBe(MODELS.codexPresentation);
    expect(p0Effort).toBe("high");
    expect(outlineAttempts).toBe(2);
    expect(batchOmissionExercised).toBe(true);
    expect(singleRecoveryCalls).toBe(1);
    const bib = await readFile(join(dir, "references.bib"), "utf8");
    expect(bib).toContain("robins1994");
    const layer = await readFile(join(dir, "formal_layer.tex"), "utf8");
    expect(layer).toMatch(/^% DERIVED from formal_layer\.json/);
    const envs = parseAnchoredEnvs(layer);
    expect(envs.length).toBeGreaterThan(20);
    // Every env has a non-empty body. (Loose nodes carry the stub render's "Touched statement body.";
    // nodes the bank locked with a P3-validated `nl.frozen_body` are used verbatim, so the body text
    // varies — assert non-emptiness rather than a fixed string.)
    expect(envs.every((e) => e.body.trim().length > 0)).toBe(true);
    const looseEnvs = envs.filter((e) => e.body.includes("Touched statement body."));
    expect(looseEnvs.length).toBeGreaterThan(0);
    // The freeze lives in the JSON formal layer (each env block's canonical body).
    const layerSrc = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    expect(layerSrc.blocks.filter((b) => b.env).length).toBe(envs.length);
  });

  it("P1 re-entry restores planned section homes instead of retaining a previous hoist", async () => {
    const dir = await dirP;
    const path = join(dir, "outline.md");
    const original = await readFile(path, "utf8");
    const outline = parseOutline(original);
    expect(outline.sections.every(s => s.homeObjs !== undefined)).toBe(true);
    const home = outline.sections.find(s => /^Auxiliary/.test(s.name))!;
    const target = home.homeObjs![0];
    expect(target).toBeDefined();
    const setup = outline.sections.find(s => s.name === "Setup and assumptions")!;
    const hoisted = new Map(outline.sections.map(s => [s.name, s.objs.filter(id => id !== target)]));
    hoisted.get(setup.name)!.unshift(target);
    await writeFile(path, rewriteOutlineObjs(original, hoisted));
    const previousPlans = outlineAttempts;
    await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, from: "P1", auto: true, stopAfter: "P1", outDir: dir });
    const restored = parseOutline(await readFile(path, "utf8"));
    expect(outlineAttempts).toBe(previousPlans);
    expect(restored.sections.find(s => s.name === home.name)!.objs).toContain(target);
    expect(restored.sections.find(s => s.name === setup.name)!.objs).not.toContain(target);
    expect(restored.sections.map(s => s.homeObjs)).toEqual(outline.sections.map(s => s.homeObjs));
    const stableOutline = await readFile(path, "utf8");
    let calls = 0;
    await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC,
      deps: { ...deps, runCodex: async args => { calls++; return deps.runCodex(args); } },
      from: "P1", auto: true, stopAfter: "P1", outDir: dir });
    expect(calls).toBe(0);
    expect(await readFile(path, "utf8")).toBe(stableOutline);
  });

  it("P2 assembles a lint-clean paper.tex and halts at draft checkpoint", async () => {
    const dir = await dirP;
    // Reference normalization applies to authored prose, then the frozen source is restored.
    // This reproduces the live incident where global normalization stripped intentional math
    // wrappers from a canonical environment after it had already been restored.
    const layerPath = join(dir, "formal_layer.json");
    const seededLayer = JSON.parse(await readFile(layerPath, "utf8"));
    const frozenTarget = seededLayer.blocks.find((b: any) => b.env === "definitionv");
    const referenceTarget = seededLayer.blocks.find((b: any) => b.obj_id !== frozenTarget.obj_id);
    const citedInlineLemma = seededLayer.blocks.find((b: any) => b.env === "lemmav");
    expect(frozenTarget).toBeDefined();
    expect(referenceTarget).toBeDefined();
    expect(citedInlineLemma).toBeDefined();
    sectionReferenceNormalizationTarget = referenceTarget.obj_id;
    frozenTarget.body += ` Canonical wrapped \\(\\cref{obj:${referenceTarget.obj_id}}\\).`;
    citedInlineLemma.cited_dependencies = [{
      node_id: "cite:fixture", cite_id: "cite:fixture", cite_key: "robins1994",
      locator: "Lemma 1", statement: "Published fixture input.", status: "matched",
    }];
    await writeFile(layerPath, JSON.stringify(seededLayer));
    const outlinePath = join(dir, "outline.md");
    const seededOutline = await readFile(outlinePath, "utf8");
    await writeFile(outlinePath, seededOutline.replace(
      "## section: Auxiliary lemmas", "## section: Appendix: Auxiliary lemmas",
    ));
    const runP2 = () => runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, resume: true, outDir: dir });
    // The ballast gate is an operator checkpoint: whichever entry is banked, a stub operator
    // acknowledges every delivered result the gate lists and the draft proceeds.
    const r = await runP2().catch(async (err: unknown) => {
      const message = err instanceof Error ? err.message : String(err);
      const listed = /P2 ballast gate: .*?\[([^\]]+)\]/.exec(message);
      if (!listed) throw err;
      const acknowledged = Object.fromEntries(listed[1].split(",").map((id) => [id.trim(), "stub operator: delivered result kept"]));
      await writeFile(join(dir, "ballast_review.json"), JSON.stringify({ acknowledged }), "utf8");
      return runP2();
    });
    expect(r.halt).toBe("checkpoint:draft");
    const paper = await readFile(join(dir, "paper.tex"), "utf8");
    const pool = parseBib(await readFile(join(dir, "references.bib"), "utf8")).map((entry) => entry.key);
    expect(paper).toContain("\\begin{abstract}");
    expect(paper).toContain("\\appendix");
    expect(paper).toContain("\\begin{proof}");
    // The D-stage informal derivation must reach every individual proof-render prompt,
    // and for this real bank entry it must be the actual derivation, not the placeholder
    // (the pre-2026-08 renderer reconstructed prose from tactic scripts alone).
    // At least one result carries a real derivation; a cited result may have none recorded.
    expect(derivationSeen.length).toBeGreaterThan(0);
    expect(derivationSeen.some(Boolean)).toBe(true);

    // The D-stage narrative layer reaches the section drafter (at least one section with
    // real per-result notes) and the front-matter author (real contribution narrative).
    expect(sectionNotesSeen.some(Boolean)).toBe(true);
    expect(frontNarrativeSeen).toBe(true);
    // Frozen bodies come from the JSON formal layer (per-block body), keyed by env obj_id.
    const layerSrc = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    const frozen = new Map<string, string>(
      layerSrc.blocks.filter((b) => b.env).map((b) => [b.obj_id, b.body]),
    );
    const citableIds = layerSrc.blocks
      .filter((b) => b.env && ["lemmav", "theoremv", "propositionv"].includes(b.env))
      .map((b) => b.obj_id);
    expect(mainProofCitableSets.length).toBeGreaterThan(0);
    expect(mainProofCitableSets.some(({ targetEnv }) => targetEnv === "propositionv")).toBe(true);
    for (const { target, seen, catalog, exactLean, targetedLookup } of mainProofCitableSets) {
      for (const id of citableIds) expect(seen.includes(id) || catalog.includes(id)).toBe(true);
      expect(exactLean).toBe(true);
      expect(targetedLookup).toBe(true);
      expect(seen.filter((id) => id === target)).toHaveLength(1);
    }
    const known = new Set(
      parseAnchoredEnvs(await readFile(join(dir, "formal_layer.tex"), "utf8")).map((e) => e.obj_id),
    );
    expect(lintAnchors(paper, known, frozen)).toEqual([]);
    expect(applyProseRevision({
      before: paper,
      revised: paper,
      blocks: layerSrc.blocks,
      auditedProofs: proofBlocks(paper),
      who: "P2 integration fixed-point",
    })).toBe(paper);
    const scopeNote = citedScopeFootnote(citedInlineLemma);
    const citedEnvAt = paper.indexOf(`\\begin{lemmav}{${citedInlineLemma.obj_id}}`);
    const citedEnvEnd = paper.indexOf("\\end{lemmav}", citedEnvAt);
    const scopeAt = paper.indexOf(scopeNote, citedEnvAt);
    const citedProofAt = paper.indexOf(
      `\\begin{proof}[Proof of \\cref{obj:${citedInlineLemma.obj_id}}]`, citedEnvAt,
    );
    expect(citedEnvAt).toBeGreaterThanOrEqual(0);
    expect(citedEnvEnd).toBeGreaterThan(citedEnvAt);
    expect(scopeAt).toBeGreaterThan(citedEnvEnd);
    expect(citedProofAt).toBeGreaterThan(scopeAt);
    expect(parseAnchoredEnvs(paper).find((e) => e.obj_id === frozenTarget.obj_id)?.body.trim())
      .toBe(frozenTarget.body.trim());
    expect(paper).toContain(`Prose stub \\cref{obj:${referenceTarget.obj_id}}.`);
    expect(paper).not.toContain(`Prose stub \\(\\cref{obj:${referenceTarget.obj_id}}\\).`);

    // Both ordinary cache-hit re-entry and authored-source reassembly preserve the same split:
    // normalized prose, byte-exact frozen environment, and no section-author call.
    sectionDraftCalls = 0;
    const cacheHit = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps,
      from: "P2", auto: true, stopAfter: "P2", outDir: dir });
    expect(cacheHit.halt).toBe("stopped:P2");
    expect(sectionDraftCalls).toBe(0);
    let rerendered = await readFile(join(dir, "paper.tex"), "utf8");
    expect(parseAnchoredEnvs(rerendered).find((e) => e.obj_id === frozenTarget.obj_id)?.body.trim())
      .toBe(frozenTarget.body.trim());
    const reassembled = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps,
      from: "P2", auto: true, stopAfter: "P2", outDir: dir });
    expect(reassembled.halt).toBe("stopped:P2");
    expect(sectionDraftCalls).toBe(0);
    rerendered = await readFile(join(dir, "paper.tex"), "utf8");
    expect(parseAnchoredEnvs(rerendered).find((e) => e.obj_id === frozenTarget.obj_id)?.body.trim())
      .toBe(frozenTarget.body.trim());
    expect(rerendered).toContain(`Prose stub \\cref{obj:${referenceTarget.obj_id}}.`);
    // This is the actual P2 stage call, rather than a hand-copied prompt-variable contract. The
    // final pool includes provenance injections appended during P2, and must be what the last
    // (front-matter) drafting call receives.
    const injectedKeys = pool.filter((key) => key !== "robins1994");
    expect(injectedKeys.length).toBeGreaterThan(0);
    expect(frontMatterPrompt).not.toContain("{{allowed_bib_keys}}");
    for (const key of pool) expect(frontMatterPrompt).toContain(key);
    expect(frontMatterPrompt).toContain("Cite ONLY the allowed bibliography keys above.");
    expect(frontMatterPrompt).toContain("may name works removed from the verified bibliography");
    expect(frontMatterPrompt).not.toContain("\\begin{proof}");
    expect(frontMatterPrompt).toContain("\\appendix");
    expect(frontMatterPrompt).toContain("\\section{Proofs of the main results}");

    // Sources are canonical: `--from P2` over an existing front_matter.tex reassembles it
    // verbatim, whatever changed upstream. A fresh draft is requested by deleting the file,
    // and this second real P2 invocation must then build the prompt from the CURRENT pool.
    frontMatterCalls = 0;
    await appendFile(join(dir, "references.bib"), "\n@article{new2026, title = {New}, author = {Author}, year = {2026}}\n", "utf8");
    const kept = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, from: "P2", auto: true, stopAfter: "P2", outDir: dir });
    expect(kept.halt).toBe("stopped:P2");
    expect(frontMatterCalls).toBe(0);
    await rm(join(dir, "front_matter.tex"));
    const rerun = await runPaperPipeline({
      repoRoot: root,
      qid: QID,
      spec: SPEC,
      deps,
      from: "P2",
      auto: true,
      stopAfter: "P2",
      outDir: dir,
    });
    expect(rerun.halt).toBe("stopped:P2");
    expect(frontMatterCalls).toBe(1);
    expect(frontMatterPrompt).toContain("new2026");
  });

  it("keeps symbol-linked prose identical in sources and assembly so exact repairs survive reentry", async () => {
    const dir = await mkdtemp(join(await dirP, "symbol-source-"));
    const seed = () => runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC,
      deps, auto: true, stopAfter: "P2", outDir: dir });
    await seed().catch(async (err: unknown) => {
      const listed = /P2 ballast gate: .*?\[([^\]]+)\]/.exec(String(err));
      if (!listed) throw err;
      await writeFile(join(dir, "ballast_review.json"), JSON.stringify({ acknowledged:
        Object.fromEntries(listed[1].split(",").map(id => [id.trim(), "stub operator: delivered result kept"])) }));
      await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC,
        deps, from: "P2", auto: true, stopAfter: "P2", outDir: dir });
    });
    const sectionName = (await readdir(join(dir, "sections"))).find(name => name.endsWith(".tex"))!;
    const sectionPath = join(dir, "sections", sectionName);
    const original = await readFile(sectionPath, "utf8");
    const prose = String.raw`The symbol \leanref{sym:fixture}{${"$"}x${"$"}} denotes the local quantity.`;
    await writeFile(sectionPath, `${original}\n${prose}\n`);
    const proofCache = await readFile(join(dir, "proof_audit_cache.json"), "utf8");
    const noModels = { ...deps, runCodex: async () => { throw new Error("unchanged reassembly dispatched a model"); } };
    const reassemble = () => runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC,
      deps: noModels, from: "P2", auto: true, stopAfter: "P2", outDir: dir });
    expect((await reassemble()).halt).toBe("stopped:P2");
    const before = String.raw`The symbol \leanref{sym:fixture}{\ensuremath{x}} denotes the local quantity.`;
    const after = before.replace("local quantity", "specified quantity");
    const authored = await readFile(sectionPath, "utf8");
    expect(authored).toContain(before);
    expect(await readFile(join(dir, "paper.tex"), "utf8")).toContain(before);
    const patched = applyTargetedReplacements(authored, [{ before, after }]);
    expect(patched.skipped).toEqual([]);
    await writeFile(sectionPath, patched.tex);
    expect((await reassemble()).halt).toBe("stopped:P2");
    expect(await readFile(join(dir, "paper.tex"), "utf8")).toContain(after);
    expect(await readFile(join(dir, "proof_audit_cache.json"), "utf8")).toBe(proofCache);

    // A cached section missing an expected environment is completed mechanically at its P1
    // position — and that never bypasses an owed proof audit.
    const complete = await readFile(sectionPath, "utf8");
    const omitted = parseAnchoredEnvs(complete)[0];
    expect(omitted).toBeDefined();
    const start = complete.indexOf(`\\begin{${omitted.env}}{${omitted.obj_id}}`);
    const closing = `\\end{${omitted.env}}`;
    const end = complete.indexOf(closing, start) + closing.length;
    await writeFile(sectionPath, complete.slice(0, start) + complete.slice(end));
    const incompleteCache = JSON.parse(proofCache);
    delete incompleteCache[Object.keys(incompleteCache)[0]];
    await writeFile(join(dir, "proof_audit_cache.json"), JSON.stringify(incompleteCache));
    await expect(reassemble()).rejects.toThrow("unchanged reassembly dispatched a model");
    await writeFile(join(dir, "proof_audit_cache.json"), proofCache);
    expect((await reassemble()).halt).toBe("stopped:P2");
    const paper = await readFile(join(dir, "paper.tex"), "utf8");
    expect(paper.split(`\\begin{${omitted.env}}{${omitted.obj_id}}`)).toHaveLength(2);
    expect(lintAnchors(paper, new Set(parseAnchoredEnvs(paper).map((e) => e.obj_id)), null)).toEqual([]);
    const stateFile = (await readdir(dir)).find((name) => name.endsWith("_paper_state.json"))!;
    const notes: string[] = JSON.parse(await readFile(join(dir, stateFile), "utf8")).notes;
    expect(notes.some((n) => n.includes(`${omitted.obj_id}: inserted at its P1 position`))).toBe(true);
  });

  it("P2 records every unrenderable proof at once and still judges its siblings", async () => {
    const dir = await mkdtemp(join(await dirP, "unclear-"));
    const seeded = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, auto: true, stopAfter: "P2", outDir: dir })
      .catch(async (err: unknown) => {
        const listed = /P2 ballast gate: .*?\[([^\]]+)\]/.exec(String(err));
        if (!listed) throw err;
        await writeFile(join(dir, "ballast_review.json"), JSON.stringify({ acknowledged:
          Object.fromEntries(listed[1].split(",").map(id => [id.trim(), "stub operator: delivered result kept"])) }));
        return runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, from: "P2", auto: true, stopAfter: "P2", outDir: dir });
      });
    expect(seeded.halt).toBe("stopped:P2");
    const proofIds = (await readdir(join(dir, "proofs"))).map(proofObjId).filter((id): id is string => id !== null);
    expect(proofIds.length).toBeGreaterThan(1);
    const [unclearId, ...others] = proofIds;
    await rm(join(dir, "proofs", proofFileName(unclearId)));
    await rm(join(dir, "proofs", "_cache_keys.json"));
    let audits = 0;
    const unclearDeps: PaperDeps = { ...deps, runCodex: async (args) => {
      if (args.prompt.includes("=== PROMPT: p2_proof ===") && args.prompt.includes(`{${unclearId}}`)) {
        return { stdout: "UNCLEAR: the Lean route branches on a case the statement does not name", stderr: "" };
      }
      if (args.prompt.includes("auditing whether a prose appendix proof faithfully")) audits++;
      return deps.runCodex(args);
    } };
    await expect(runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: unclearDeps, from: "P2", auto: true, stopAfter: "P2", outDir: dir }))
      .rejects.toThrow(new RegExp(`rendering defects remain.*1 proof\\(s\\) could not be rendered.*${unclearId}: the writer reported the Lean route UNCLEAR`));
    // Siblings were rendered (their files exist) and no sibling was left un-judged for the halt.
    for (const id of others) expect(await readFile(join(dir, "proofs", proofFileName(id)), "utf8")).toContain("\\begin{proof}");
    expect(audits).toBe(0); // every sibling approval was reused from the seeded pass
    // Re-entry renders only the unclear proof.
    let renders = 0;
    const countRenders: PaperDeps = { ...deps, runCodex: async (args) => {
      if (args.prompt.includes("=== PROMPT: p2_proof ===")) renders++;
      return deps.runCodex(args);
    } };
    expect((await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: countRenders, from: "P2", auto: true, stopAfter: "P2", outDir: dir })).halt).toBe("stopped:P2");
    expect(renders).toBe(1);
  });

  it("P1 retries an unparseable notation review once instead of failing the stage", async () => {
    const dir = await dirP;
    const cachePath = join(dir, "p1_cache.json");
    const original = await readFile(cachePath, "utf8");
    const cache = JSON.parse(original);
    cache.notation = {};
    await writeFile(cachePath, JSON.stringify(cache));
    let reviews = 0;
    const flakyDeps: PaperDeps = { ...deps, runCodex: async (args) => {
      if (args.prompt.includes("NOTATION-RESOLVABILITY")) {
        reviews++;
        if (reviews === 1) return { stdout: "I could not review this layer.", stderr: "" };
      }
      return deps.runCodex(args);
    } };
    try {
      const r = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: flakyDeps, from: "P1", auto: true, stopAfter: "P1", outDir: dir });
      expect(r.halt).toBe("stopped:P1");
      expect(reviews).toBe(2);
    } finally {
      await writeFile(cachePath, original);
    }
  });

  it("P2 does not repeat an identical failed proof repair on unchanged restart", async () => {
    const dir = await dirP;
    const cachePath = join(dir, "proof_audit_cache.json");
    // Earlier tests hand-edited the layer and re-entered P1: settle every approval on the CURRENT
    // layer first, so the row edited below is keyed as an unchanged restart would see it.
    await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, from: "P2", auto: true, stopAfter: "P2", outDir: dir });
    const original = await readFile(cachePath, "utf8");
    const cache = JSON.parse(original);
    const target = Object.keys(cache)[0];
    expect(target).toBeDefined();
    cache[target].verdict = "unfaithful";
    cache[target].issues = ["[rendering] controlled unresolved defect"];
    delete cache[target].repairStoppedKey;
    await writeFile(cachePath, JSON.stringify(cache));
    let renders = 0;
    const noProgress: PaperDeps = { ...deps, runCodex: async args => {
      if (args.prompt.includes("=== PROMPT: p2_proof ===")) {
        renders++;
        return { stdout: await readFile(join(dir, "proofs", proofFileName(target)), "utf8"), stderr: "" };
      }
      return deps.runCodex(args);
    } };
    const run = () => runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: noProgress,
      from: "P2", auto: true, stopAfter: "P2", outDir: dir });
    try {
      await expect(run()).rejects.toThrow(/proof.*rendering/i);
      expect(renders).toBe(1);
      await expect(run()).rejects.toThrow(/proof.*rendering/i);
      expect(renders).toBe(1);
    } finally {
      await writeFile(cachePath, original);
    }
  });

  it("repairs an approved body on new semantic evidence and freezes only after convergence", async () => {
    const dir = await dirP;
    const initial = parseAnchoredEnvs(await readFile(join(dir, "formal_layer.tex"), "utf8"));
    const target = initial.find((e) => e.env === "propositionv")!;
    const loaded = await loadBankEntry(root, QID, SPEC);
    const dependencies = new Set(loaded.graph.edges.filter((e) => e.from === target.obj_id && e.kind === "statement-uses").map((e) => e.to));
    const extra = initial.find((e) => e.env === "definitionv" && !dependencies.has(e.obj_id) && !target.body.includes(`obj:${e.obj_id}`))!;
    expect(extra).toBeDefined();
    const marker = "Corrected notation meaning.";
    let repairs = 0;
    const repairDeps: PaperDeps = { ...deps, runCodex: async (args) => {
      if (args.prompt.includes("=== PROMPT: p1_notation_check ===")) {
        return { stdout: JSON.stringify({ problems: args.prompt.includes(marker) ? [] : [
          { symbol: "x", case: "mismatch", used_in: [target.obj_id], fix: "Restore the intended meaning." },
        ] }), stderr: "" };
      }
      if (args.prompt.includes("=== PROMPT: p1_render_from_lean ===") || args.prompt.includes("=== PROMPT: p1_touchup ===")) {
        repairs++;
        return { stdout: `@@@ENV ${target.obj_id}@@@
TITLE: Repaired
@@@BODY@@@
${target.body} ${marker} See \\cref{obj:${extra.obj_id}}.
@@@END@@@`, stderr: "" };
      }
      return deps.runCodex(args);
    } };
    const cachePath = join(dir, "p1_cache.json");
    const cache = JSON.parse(await readFile(cachePath, "utf8"));
    cache.notation = {};
    await writeFile(cachePath, JSON.stringify(cache));
    const result = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: repairDeps,
      from: "P1", auto: true, stopAfter: "P1", outDir: dir });
    expect(result.halt).toBe("stopped:P1");
    expect(repairs).toBe(1);
    const final = parseAnchoredEnvs(await readFile(join(dir, "formal_layer.tex"), "utf8"));
    expect(final.find((e) => e.obj_id === target.obj_id)?.body).toContain(marker);
    for (const e of initial.filter((e) => e.obj_id !== target.obj_id)) {
      expect(final.find((f) => f.obj_id === e.obj_id)?.body).toBe(e.body);
    }
    const bank = await loadBankEntry(root, QID, SPEC);
    expect(bank.graph.nodes.find((n) => n.id === target.obj_id)?.nl.frozen_body).toContain(marker);

    // A subsequent unresolvable defect must halt without committing the attempted wording.
    const failedBody = "Still defective wording.";
    const failedCache = JSON.parse(await readFile(cachePath, "utf8"));
    failedCache.notation = {};
    await writeFile(cachePath, JSON.stringify(failedCache));
    const failedDeps: PaperDeps = { ...deps, runCodex: async (args) => {
      if (args.prompt.includes("=== PROMPT: p1_notation_check ===")) return {
        stdout: JSON.stringify({ problems: [{ symbol: "x", case: "mismatch", used_in: [target.obj_id], fix: "Still wrong." }] }), stderr: "",
      };
      if (args.prompt.includes("=== PROMPT: p1_render_from_lean ===")) return {
        stdout: `@@@ENV ${target.obj_id}@@@
TITLE: Attempt
@@@BODY@@@
${target.body} ${failedBody}
@@@END@@@`, stderr: "",
      };
      return deps.runCodex(args);
    } };
    await expect(runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: failedDeps,
      from: "P1", auto: true, stopAfter: "P1", outDir: dir })).rejects.toThrow(/did not converge/);
    const afterFailure = await loadBankEntry(root, QID, SPEC);
    const frozen = afterFailure.graph.nodes.find((n) => n.id === target.obj_id)?.nl.frozen_body;
    expect(frozen).toContain(marker);
    expect(frozen).not.toContain(failedBody);
  });

  it.each([true, false])("reuses interrupted repairs with candidate recovery enabled=%s", async (recoverCandidate) => {
    const dir = await dirP;
    const target = parseAnchoredEnvs(await readFile(join(dir, "formal_layer.tex"), "utf8")).find(e => e.env === "propositionv")!;
    const bank = await loadBankEntry(root, QID, SPEC);
    const approved = bank.graph.nodes.find(n => n.id === target.obj_id)!.nl.frozen_body!;
    const marker = `Restart cache witness ${recoverCandidate}.`;
    let repairs = 0;
    let interrupt = true;
    let judgeCalls = 0;
    const cachedPath = join(dir, "p1_cache.json");
    const c = JSON.parse(await readFile(cachedPath, "utf8")); c.notation = {};
    await writeFile(cachedPath, JSON.stringify(c));
    const restartDeps: PaperDeps = { ...deps, runCodex: async args => {
      if (args.prompt.includes("=== PROMPT: p1_notation_check ===")) {
        if (args.prompt.includes(marker)) {
          if (interrupt) throw new Error("intentional post-repair interruption");
          return {stdout: JSON.stringify({problems: []}), stderr: ""};
        }
        return {stdout: JSON.stringify({problems: [{symbol:"x", case:"mismatch", used_in:[target.obj_id], fix:"Write the corrected form."}]}),stderr:""};
      }
      if (args.prompt.includes("=== PROMPT: p1_render_from_lean ===") || args.prompt.includes("=== PROMPT: p1_touchup ===")) {
        repairs++;
        return {stdout:`@@@ENV ${target.obj_id}@@@\nTITLE: Repaired\n@@@BODY@@@\n${approved} ${marker}\n@@@END@@@`,stderr:""};
      }
      if (args.prompt.includes("=== PROMPT: statement_equivalence")) judgeCalls++;
      return deps.runCodex(args);
    }};
    const run = () => runPaperPipeline({repoRoot:root,qid:QID,spec:SPEC,deps:restartDeps,from:"P1",auto:true,stopAfter:"P1",outDir:dir});
    await expect(run()).rejects.toThrow("intentional post-repair interruption");
    expect(repairs).toBe(1);
    const cached = JSON.parse(await readFile(cachedPath,"utf8"));
    expect(Object.values(cached.render).some((v:any)=>v.body.includes(marker))).toBe(true);
    if (!recoverCandidate) {
      delete cached.candidates[target.obj_id]; // Legacy caches have render entries only.
      await writeFile(cachedPath, JSON.stringify(cached));
    }
    interrupt = false;
    judgeCalls = 0;
    await run();
    expect(repairs).toBe(1);
    if (recoverCandidate) expect(judgeCalls).toBe(0);
  });

  it("persists a successful sibling render even when another throws", async () => {
    const dir = await dirP;
    const envs = parseAnchoredEnvs(await readFile(join(dir,"formal_layer.tex"),"utf8"));
    const targets = envs.filter(e=>["theoremv","propositionv","lemmav"].includes(e.env)).slice(0,2);
    expect(targets).toHaveLength(2);
    const marker = "Successful sibling repair.";
    const cachePath=join(dir,"p1_cache.json"); const c=JSON.parse(await readFile(cachePath,"utf8")); c.notation={}; await writeFile(cachePath,JSON.stringify(c));
    let completed=0;
    let release!:()=>void;
    const firstDone=new Promise<void>(r=>{release=r});
    const failDeps: PaperDeps={...deps,runCodex:async args=>{
      if(args.prompt.includes("=== PROMPT: p1_notation_check ===")) return {stdout:JSON.stringify({problems:[{symbol:"x",case:"mismatch",used_in:targets.map(t=>t.obj_id),fix:"Repair the meaning."}]}),stderr:""};
      if(args.prompt.includes("=== PROMPT: p1_render_from_lean ===")) {
        const id=args.prompt.match(/Object: ([^\s]+)/)?.[1];
        if(id===targets[0].obj_id){completed++;release!();return {stdout:`@@@ENV ${id}@@@\nTITLE: Repaired\n@@@BODY@@@\n${targets[0].body} ${marker}\n@@@END@@@`,stderr:""};}
        if(id===targets[1].obj_id){await firstDone;throw new Error("intentional sibling render failure");}
      }
      return deps.runCodex(args);
    }};
    await expect(runPaperPipeline({repoRoot:root,qid:QID,spec:SPEC,deps:failDeps,from:"P1",auto:true,stopAfter:"P1",outDir:dir})).rejects.toThrow("intentional sibling render failure");
    expect(completed).toBe(1);
    const cached=JSON.parse(await readFile(cachePath,"utf8"));
    expect(Object.values(cached.render).some((v:any)=>v.body.includes(marker))).toBe(true);
  });

  it("never restores an interrupted candidate over a newer bank edit", async () => {
    const dir = await dirP;
    const cache = JSON.parse(await readFile(join(dir, "p1_cache.json"), "utf8"));
    const bank = await loadBankEntry(root, QID, SPEC);
    const node = bank.graph.nodes.find((n) => cache.candidates?.[n.id] &&
      cache.render[cache.candidates[n.id].renderKey]?.body.includes("Successful sibling repair."))!;
    expect(node).toBeDefined();
    node.nl.frozen_body = `${node.nl.frozen_body} New bank wording.`;
    await saveGraph(graphPath(bank.dir, QID, SPEC), bank.graph);
    cache.notation = {};
    await writeFile(join(dir, "p1_cache.json"), JSON.stringify(cache));
    let reviewed = "";
    await expect(runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, from: "P1", auto: true,
      stopAfter: "P1", outDir: dir, deps: { ...deps, runCodex: async (args) => {
        if (args.prompt.includes("=== PROMPT: p1_notation_check ===")) {
          reviewed = args.prompt;
          throw new Error("stop after observing selected candidate");
        }
        return deps.runCodex(args);
      } } })).rejects.toThrow("stop after observing selected candidate");
    expect(reviewed).toContain("New bank wording.");
    expect(reviewed).not.toContain("Successful sibling repair.");
  });

  it("reuses valid promoted homes despite a stale planner key and replans missing objects", async () => {
    const dir = await mkdtemp(join(await dirP, "promoted-homes-"));
    const priorBank = isolatedBank.dir;
    isolatedBank.dir = join(dir, "bank");
    try {
      await copyBankFixture(isolatedBank.dir);
      await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps,
        auto: true, stopAfter: "P1", outDir: dir });
      const graphFile = graphPath(isolatedBank.dir, QID, SPEC);
      const graph = JSON.parse(await readFile(graphFile, "utf8"));
      const template = graph.nodes.find((n: any) => n.kind === "lemma" && n.nl?.frozen !== false && n.lean?.decl_name);
      expect(template).toBeDefined();
      const promotedId = "lem:fixture-promoted-helper";
      graph.nodes.push({ ...structuredClone(template), id: promotedId });
      await writeFile(graphFile, JSON.stringify(graph));
      const outlinePath = join(dir, "outline.md");
      const before = await readFile(outlinePath, "utf8");
      const outline = parseOutline(before);
      const homes = new Map(outline.sections.map(s => [s.name, [...(s.homeObjs ?? s.objs)]]));
      const resolved = new Map(outline.sections.map(s => [s.name, [...s.objs]]));
      const appendix = outline.sections.find(s => /^Auxiliary/.test(s.name))!.name;
      homes.get(appendix)!.unshift(promotedId);
      resolved.get(appendix)!.unshift(promotedId);
      await writeFile(outlinePath, rewriteOutlineObjs(before, resolved, homes));
      const cachePath = join(dir, "p1_cache.json");
      const cache = JSON.parse(await readFile(cachePath, "utf8"));
      cache.outlineStructureKey = "stale-legacy-key";
      await writeFile(cachePath, JSON.stringify(cache));
      let plannerCalls = 0;
      const trackedDeps: PaperDeps = { ...deps, runCodex: async args => {
        if (args.prompt.includes("=== PROMPT: p1_plan ===")) plannerCalls++;
        return deps.runCodex(args);
      } };
      await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: trackedDeps,
        from: "P1", auto: true, stopAfter: "P1", outDir: dir });
      expect(plannerCalls).toBe(0);
      const preserved = parseOutline(await readFile(outlinePath, "utf8"));
      expect(new Map(preserved.sections.map(s => [s.name, s.homeObjs]))).toEqual(homes);

      // Artifact validation remains binding: a missing graph object requires a fresh plan.
      const invalidHomes = new Map([...homes].map(([name, ids]) => [name, ids.filter(id => id !== promotedId)]));
      await writeFile(outlinePath, rewriteOutlineObjs(before, invalidHomes, invalidHomes));
      await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: trackedDeps,
        from: "P1", auto: true, stopAfter: "P1", outDir: dir });
      expect(plannerCalls).toBe(1);
      const repaired = parseOutline(await readFile(outlinePath, "utf8"));
      expect(repaired.sections.flatMap(s => s.homeObjs ?? s.objs).filter(id => id === promotedId)).toHaveLength(1);
    } finally {
      isolatedBank.dir = priorBank;
    }
  });

  it("halts P1 on missing Lean coverage before any wording repair and preserves the accepted body", async () => {
    const dir = await mkdtemp(join(await dirP, "coverage-"));
    const priorBank = isolatedBank.dir;
    isolatedBank.dir = join(dir, "bank");
    try {
      await copyBankFixture(isolatedBank.dir);
      // Bootstrap this regression's own P0/P1 artifacts, including the related-work brief.
      await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps,
        auto: true, stopAfter: "P1", outDir: dir });
      const initial = parseAnchoredEnvs(await readFile(join(dir, "formal_layer.tex"), "utf8"));
      const target = initial.find((e) => e.env === "theoremv")!;
      const graphFile = graphPath(isolatedBank.dir, QID, SPEC);
      const bankBefore = await readFile(graphFile, "utf8");
      const cachePath = join(dir, "equivalence_cache.json");
      const cache = JSON.parse(await readFile(cachePath, "utf8"));
      delete cache[target.obj_id];
      await writeFile(cachePath, JSON.stringify(cache));
      const p1CachePath = join(dir, "p1_cache.json");
      const p1Cache = JSON.parse(await readFile(p1CachePath, "utf8"));
      p1Cache.notation = {};
      await writeFile(p1CachePath, JSON.stringify(p1Cache));
      let repairs = 0;
      let judgments = 0;
      let dispatches = 0;
      const coverageDeps: PaperDeps = { ...deps, runCodex: async (args) => {
        dispatches++;
        if (args.prompt.includes("=== PROMPT: statement_equivalence ===") &&
            args.prompt.includes(`Paper environment body (${target.obj_id})`)) {
          judgments++;
          return { stdout: JSON.stringify({ verdict: "missing-coverage",
            detail: "Estimator.measurable supports the Borel clause but is absent from the mapped pieces." }), stderr: "" };
        }
        if (args.prompt.includes("=== PROMPT: p1_notation_check ===")) return {
          stdout: JSON.stringify({ problems: [{ symbol: "x", case: "mismatch",
            used_in: [target.obj_id], fix: "A simultaneous wording repair must wait for source coverage." }] }), stderr: "",
        };
        if (args.prompt.includes("=== PROMPT: p1_render_from_lean ===") || args.prompt.includes("=== PROMPT: p1_touchup ===")) {
          repairs++;
          throw new Error("Missing source coverage must never reach the body renderer");
        }
        return deps.runCodex(args);
      } };
      await expect(runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: coverageDeps,
        from: "P1", auto: true, stopAfter: "P1", outDir: dir })).rejects.toThrow(/\[lean-coverage\].*Estimator.measurable/);
      const firstDispatches = dispatches;
      await expect(runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: coverageDeps,
        from: "P1", auto: true, stopAfter: "P1", outDir: dir })).rejects.toThrow(/\[lean-coverage\].*Estimator.measurable/);
      expect(dispatches).toBe(firstDispatches); // Unchanged restart has no paid work, including the blocked judge.
      expect(judgments).toBe(1);
      expect(repairs).toBe(0);
      const final = parseAnchoredEnvs(await readFile(join(dir, "formal_layer.tex"), "utf8"));
      expect(final.find((e) => e.obj_id === target.obj_id)?.body).toBe(target.body);
      expect(await readFile(graphFile, "utf8")).toBe(bankBefore);
      expect(JSON.parse(await readFile(join(dir, "notation_review.json"), "utf8")).iterations).toBe(1);
    } finally {
      isolatedBank.dir = priorBank;
    }
  });

});

describe("parseNotationReviewerOutput (P1 reviewer JSON boundary)", () => {
  it("returns problems array when present", () => {
    expect(parseNotationReviewerOutput('{"problems":[{"symbol":"G_n","case":"undefined"}]}'))
      .toEqual([{ symbol: "G_n", case: "undefined" }]);
  });
  it("accepts an explicit clean verdict without problems", () => {
    expect(parseNotationReviewerOutput('{"clean": true}')).toEqual([]);
    expect(parseNotationReviewerOutput('{"problems": []}')).toEqual([]);
  });
  it("throws on non-JSON output instead of passing as clean", () => {
    expect(() => parseNotationReviewerOutput("I could not review this layer."))
      .toThrow(/notation reviewer/);
  });
  it("throws on the contradictory clean:false with empty problems instead of passing as clean", () => {
    // The reviewer found problems but listed them in prose (or emitted an unfilled
    // skeleton) — the only notation check must fail loud (audit, 2026-08-26).
    expect(() => parseNotationReviewerOutput('{"clean": false, "problems": []}')).toThrow(/notation reviewer/);
  });
  it("throws when neither clean:true nor a problems array is present", () => {
    expect(() => parseNotationReviewerOutput('{"clean": false}')).toThrow(/notation reviewer/);
  });
});
