import { MODELS } from "../../models.js";
import { readFile, writeFile, mkdir } from "node:fs/promises";
import { join } from "node:path";
import type { StageIO } from "../pipeline.js";
import { PRESENTATION_PROSE_POLICY_VERSION, presentationPrompt, promptFingerprint } from "../prompt_io.js";
import { parseOutline, unwrapArtifact, lintMainBodyDependencies, type Outline } from "../stage_util.js";
import {
  lintAnchors,
  lintClarity,
  lintSelfContainment,
  lintCrossRefs,
  lintReferences,
  normalizeCrefs,
  repairObjRefs,
  lintHypothesisPresentation,
  hashEnvBody,
  containsNotation,
  type LintProblem,
} from "../tex_anchors.js";
import { parseBib } from "../citations.js";
import { parseJsonLoose, mapLimit } from "../gates.js";
import { NOTATION_REPLY } from "../reply_schemas.js";
import { parseSynthReply } from "../synth_reply.js";
import { buildLeanContextIndex, type LeanContext } from "../lean_context.js";
import { citedDependencies, renderedNodes, topoOrder, refTargets, envForNode, isCitedNode } from "../graph_view.js";
import { citedStdFromNode, reconcileCite, indexBib } from "../assumption_citations.js";
import { FIRST_DRAFT_BRIEF } from "../revision_brief.js";
import { blocksFromGraph, blocksToTex, FormalLayerSource, type FormalBlock } from "../formal_layer.js";
import {
  runP1Loop,
  renderMechanicalLayer,
  atomicRequestedNotationSymbols,
  isAdvisoryFinding,
  type P1Env,
  type P1Finding,
  type P1LoopHooks,
} from "../p1_loop.js";
import { judgeStatements, persistFrozenBodies, type StatementJudgement, type StatementLeanContext } from "../audit.js";
import { paperOrder, insertSynths, repairDefinitionOrder, sectionObjs, rewriteOutlineObjs, outlineForPlanning, isSynthId } from "../p1_order.js";
import { writeJsonAtomic, writeTextAtomic } from "../json_io.js";
import { loadJsonCache } from "../cache.js";
import { loadBankNarrative } from "../bank.js";
import { discoverRealizedSymbols, buildSymbolClusters } from "../../formalization/crosswalk.js";
import { buildModuleDeclIndex } from "../components.js";
import { resolveSymbolHomes, type SymbolLeanHome } from "../synth_lean_match.js";

const OPEN_DIRECTION_RE = /\b(?:open (?:question|problem|direction)|unresolved (?:question|issue)|remains? (?:open|unknown|unresolved)|remain(?:s)? to (?:be )?(?:shown|determined|understood|resolved)|ask(?:s|ed)? whether|question (?:is|of) whether|future work|further work|future research|next step|worth (?:investigating|studying)|natural (?:question|direction|extension|strengthening))\b/i;
const ASSERTED_RESULT_RE = /\b(?:(?:we|this (?:paper|work)|our (?:paper|work|result|analysis))\s+(?:prove|proves|establish|establishes|show|shows|derive|derives|demonstrate|demonstrates)|(?:theorem|corollary|proposition|our result)\b[^.!?]{0,100}\b(?:prove|proves|establish|establishes|show|shows|imply|implies)|it follows that|we conclude that|is established here|has been proved)\b/i;
const ASSERTIVE_REVERSAL_RE = /\b(?:nevertheless|in fact|indeed|therefore|thus|hence)\b/i;
const LEGALISTIC_UNDELIVERED_RE = /^\s*this work does not (?:establish|prove|deliver)/i;

/** A model-written remark is acceptable only when it clearly frames the claim as an open
 * direction and does not turn around and assert it as a theorem/result. */
export function safelyFramesUndeliveredRemark(body: string): boolean {
  const text = body.trim();
  return text.length > 0 && OPEN_DIRECTION_RE.test(text) && !ASSERTED_RESULT_RE.test(text) && !ASSERTIVE_REVERSAL_RE.test(text) && !LEGALISTIC_UNDELIVERED_RE.test(text);
}

/** Boundary parse of the P1 notation-reviewer reply. An unusable reply must throw,
 *  not collapse to a clean review: this path previously defaulted to `[]`, so a
 *  reviewer that answered in prose silently passed the notation gate. */
export interface NotationReviewerProblem { symbol?: string; used_in?: string[]; case?: string; fix?: string }
export function parseNotationReviewerOutput(stdout: string): NotationReviewerProblem[] {
  const parsed = parseJsonLoose(stdout) as { clean?: unknown; problems?: unknown } | null;
  if (parsed === null) {
    throw new Error("P1 notation reviewer output is not parseable JSON — re-run P1 (inputs are cached)");
  }
  // The CONTRADICTORY reply `{"clean": false, "problems": []}` (problems reported in prose,
  // or an unfilled skeleton) must fail loud, never collapse to a clean review — this is the
  // stage's ONLY notation check. An empty problems array WITHOUT `clean: false` stays accepted
  // as clean (long-pinned contract).
  if (Array.isArray(parsed.problems) && (parsed.problems.length > 0 || parsed.clean !== false)) {
    return parsed.problems as NotationReviewerProblem[];
  }
  if (parsed.clean === true) return [];
  throw new Error("P1 notation reviewer output has neither clean:true nor a usable problems array — re-run P1");
}

/** Reader-facing rendering of a node this run explicitly does not deliver. The agent normally
 * supplies varied prose; deterministic variants are only the fail-closed fallback for an unsafe
 * or missing render. Previously frozen theorem bodies never cross this boundary. */
export function undeliveredRemarkBody(statement: string, reason: string, candidate?: string): string {
  if (candidate && safelyFramesUndeliveredRemark(candidate)) return candidate.trim();
  const claim = statement.trim().replace(/\s+/g, " ");
  const why = reason.trim().replace(/^[a-z0-9-]+:\s*/i, "").replace(/\s+/g, " ");
  const variants = [
    `A natural open question is whether the following proposed conclusion holds: \\emph{${claim}}. Addressing it would require ${why}, and we leave it for future work.`,
    `It remains open in the present framework whether \\emph{${claim}}. The missing ingredient is ${why}; resolving it is a direction for further work.`,
    `One worthwhile direction for future research is to determine whether \\emph{${claim}}. Doing so requires ${why}, which lies beyond the present development.`,
  ];
  const variant = [...claim].reduce((sum, ch) => sum + ch.codePointAt(0)!, 0) % variants.length;
  return variants[variant];
}

/** Select the final JSON/TeX body without letting a stale theorem freeze override a newly
 * undelivered remark. Kept pure so the final-emission boundary has direct regression coverage. */
export function presentedBody(
  deliveryStatus: string | undefined,
  frozenBody: string | undefined,
  loopBody: string | undefined,
): string {
  return deliveryStatus === "undelivered" ? (loopBody ?? "") : (frozenBody ?? loopBody ?? "");
}

/** Outline must place every graph env exactly once and cite only pool keys. Synth ids may appear
 *  (a previous run wrote them) or not — P1 places them mechanically either way. */
function validateOutline(outlineMd: string, ids: string[], poolKeys: Set<string>): string[] {
  const problems: string[] = [];
  const outline = parseOutline(outlineMd);
  if (!outlineMd.trimStart().startsWith("# Title")) {
    problems.push("outline does not start with `# Title` — output-format drift");
  }
  if (outline.sections.length < 3) problems.push(`only ${outline.sections.length} sections parsed`);
  // Names are compared by their file slug: P2 keys section files on it, so "Main Results" and
  // "Main results" would share one file (and one prior draft) even though they differ as strings.
  const slugs = outline.sections.map((s) => s.name.toLowerCase().replace(/[^a-z0-9]+/g, "_"));
  for (const dup of new Set(slugs.filter((n, i) => slugs.indexOf(n) !== i))) {
    problems.push(`section name "${outline.sections[slugs.indexOf(dup)].name}" appears more than once up to case/punctuation (objs lines and section files are keyed by section name)`);
  }
  const placed = outline.sections.flatMap((s) => s.objs);
  for (const id of ids) {
    const n = placed.filter((p) => p === id).length;
    if (n !== 1) problems.push(`obj ${id} placed ${n} times (must be exactly 1)`);
  }
  for (const extra of placed.filter((p) => !ids.includes(p) && !isSynthId(p))) {
    problems.push(`obj ${extra} is not in the frozen layer`);
  }
  for (const key of new Set(outline.sections.flatMap((s) => s.bib))) {
    if (!poolKeys.has(key)) problems.push(`bib key ${key} is not in the citation pool`);
  }
  // Abstract and introduction are written last from the finished body and carry no environments:
  // an obj placed there would never be drafted and would surface only at assembly.
  for (const s of outline.sections) {
    if (/^(abstract|introduction)$/i.test(s.name) && s.objs.length > 0) {
      problems.push(`section "${s.name}" places ${s.objs.join(", ")} — the abstract and introduction carry no formal environments; place them in a body section`);
    }
  }
  return problems;
}

/** Route notation defects to the owning writer. Cached bodies remain repairable; only a
 * missing mathematical definition creates a new environment. Unknown targets fail explicitly. */
export function routeNotationProblems(
  problems: NotationReviewerProblem[],
  opts: { knownIds: ReadonlySet<string>; definitionFor?: (symbol: string) => string | undefined },
): P1Finding[] {
  return problems.flatMap<P1Finding>((p) => {
    const symbol = p.symbol;
    // The reviewer names environments as the paper cites them (`obj:<id>`) or bare; the layer's
    // ids are bare. Normalize, or every finding on a second round halts as "invalid environment".
    const usedIn = [...new Set((p.used_in ?? []).map((id) => id.replace(/^obj:/, "")))];
    const detail = `${symbol ?? "?"} [${p.case ?? "?"}] in ${usedIn.join("/")} — ${p.fix ?? ""}`;
    if (!symbol || !usedIn.length || usedIn.some((id) => !opts.knownIds.has(id))) {
      return [{ gate: "notation-reviewer", symbol, fixLocus: "halt", detail: `${detail} (missing symbol or invalid using environment)` }];
    }
    if (p.case === "undefined" || p.case === "no-anchor") {
      const atoms = atomicRequestedNotationSymbols(symbol);
      if (atoms.length === 0) {
        return [{ gate: "notation-reviewer", symbol, fixLocus: "halt", detail: `${detail} (symbol has no synthesizable atom)` }];
      }
      return atoms.map((atom): P1Finding => {
        const home = opts.definitionFor?.(atom);
        return home
          ? { gate: "notation-reviewer", objId: home, symbol: atom, usedIn, fixLocus: "wording-revise", detail }
          : { gate: "notation-reviewer", symbol: atom, usedIn, fixLocus: "synthesize-def", detail };
      });
    }
    if (p.case === "wrong-ref" || p.case === "mismatch" || p.case === "rendering") {
      return usedIn.map((objId) => ({ gate: "notation-reviewer", objId, symbol, fixLocus: "wording-revise" as const, detail }));
    }
    return [{ gate: "notation-reviewer", symbol, fixLocus: "halt", detail }];
  });
}

/** Convert a deterministic LintProblem to a loop finding (gate/objId/detail carry over). */
const toFinding = (p: LintProblem): P1Finding => ({ gate: p.gate, objId: p.objId, detail: p.detail });

/** Failure-path diagnostic dumps land under logs/ so the bundle root stays durable-only. */
async function writeDiagnostic(outDir: string, name: string, content: string): Promise<void> {
  const dir = join(outDir, "logs");
  await mkdir(dir, { recursive: true });
  await writeFile(join(dir, name), content, "utf8");
}

/** TRUE iff a body is already written as numbered steps — i.e. it IS an algorithm box.
 *  Gates whether the `algorithmv` body lock is released: released to CREATE the box from
 *  unstepped prose, kept once P3 has validated and frozen a stepped body, so a verified box
 *  is not re-rolled on every planning entry. */
export const isSteppedBodyForTest = (body: string): boolean => /\\begin\{enumerate\}|\\item\b/.test(body);

/** P1 render-cache key (NL touch-up). `envHint` is appended ONLY when non-empty so objects without
 * an env override hash byte-identically to the legacy formula. The notation table is deliberately
 * NOT a key input: it is a style hint to the renderer, the reviewer judges the result, and a table
 * edit alone must not re-roll every validated body. */
export function renderCacheKey(
  renderModelKey: string,
  r: { statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: unknown },
  citedPrompt: string,
  envHint: string,
): string {
  return hashEnvBody([
    renderModelKey,
    r.statement,
    [...r.refSet].sort().join(","),
    r.priorBody ?? "",
    (r.defects ?? []).join("|"),
    JSON.stringify(r.delivery ?? null),
    citedPrompt,
    ...(envHint ? [envHint] : []),
  ].join("§"));
}

/** Cache key for bodies rendered from Lean: every semantic prompt input except the notation table
 * (see `renderCacheKey`) — the Lean counterpart and its referenced definitions, the NL statement,
 * the ref set, the cited-dependency text, and the prior body + defects of a repair. */
export function leanRenderCacheKey(
  renderModelKey: string,
  r: { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: unknown },
  ctx: { statement: string; referencedDefs: string },
  kind: string,
  citedPrompt: string,
): string {
  return hashEnvBody([
    renderModelKey,
    r.id,
    kind,
    ctx.statement,
    ctx.referencedDefs,
    r.statement,
    [...r.refSet].sort().join(","),
    citedPrompt,
    r.priorBody ?? "",
    (r.defects ?? []).join("|"),
    JSON.stringify(r.delivery ?? null),
    "lean-render",
  ].join("§"));
}

export function shouldUseLeanRender(deliveryStatus: string | undefined, hasLeanContext: boolean): boolean {
  return hasLeanContext && deliveryStatus !== "undelivered";
}

export function p1TouchupEnvInput(input: {
  id: string;
  refSet: string[];
  citedDependencies: string;
  statement: string;
  delivery?: P1Env["delivery"];
  environmentHint?: string;
  priorBody?: string;
  defects?: string[];
}): string {
  return [
    `### ${input.id}`,
    `ref_set: ${input.refSet.join(", ") || "(none)"}`,
    `cited_dependencies: ${input.citedDependencies}`,
    input.delivery
      ? `delivery_status: ${input.delivery.status}\ndelivery_role: ${input.delivery.role ?? "secondary"}\ndelivery_reason: ${input.delivery.reason}\nenvironment: remarkv`
      : input.environmentHint ?? "",
    `statement: ${input.statement}`,
    input.priorBody ? `prior_body: ${input.priorBody}` : "",
    input.defects ? `defects: ${input.defects.join(" | ")}` : "",
  ].filter(Boolean).join("\n");
}

/** One synthesized definition as the writer returned it. */
export interface SynthGroup { symbols: string[]; title?: string; body: string }
/** A synthesized definition env, durable in `p1_cache.json` (the authored content the layer is
 *  derived from; a defect-driven re-render updates `body`). `lean` marks a definition rendered
 *  from — and judged against — the Lean declaration that realizes its symbols; absent, the
 *  definition is presentation-only prose the writer authored. */
export interface SynthEnvRecord { symbols: string[]; title?: string; body: string; lean?: { decl: string; file: string } }

/** Release cached presentation-only definitions whose symbols the Lean now resolves: the
 *  reviewer re-reports those symbols as undefined and the synthesize hook re-defines them from
 *  the Lean. The synthesis-call entries that produced the released ids go too, so a repeated
 *  request cannot replay them. Returns the released ids. */
export function releaseLeanResolvableSynths(
  cache: Pick<P1Cache, "synth" | "synthEnvs">,
  resolves: (symbols: readonly string[]) => boolean,
): string[] {
  const released = Object.entries(cache.synthEnvs)
    .filter(([, rec]) => !rec.lean && resolves(rec.symbols))
    .map(([id]) => id);
  for (const id of released) delete cache.synthEnvs[id];
  for (const [key, call] of Object.entries(cache.synth)) {
    if (call.ids.some((id) => id !== null && released.includes(id))) delete cache.synth[key];
  }
  return released;
}

/** The P1 cache: content-keyed model outputs plus the synthesized definitions they produced. */
export interface P1Cache {
  /** Latest unaudited graph-body candidate, referencing the existing rendered output.
   * Source identity prevents an interrupted draft from overriding newer bank edits. */
  candidates?: Record<string, { sourceKey: string; renderKey: string }>;
  render: Record<string, { title?: string; body: string }>;
  notation: Record<string, NotationReviewerProblem[]>;
  /** synthesis-call key → the writer's groups and the env id each group became (null = rejected). */
  synth: Record<string, { groups: SynthGroup[]; ids: (string | null)[] }>;
  synthEnvs: Record<string, SynthEnvRecord>;
  /** Highest synth id ever minted (ids are never reused after a release). */
  synthCounter?: number;
}

/** A cache written before P1 v2 kept a per-symbol synthesis LEDGER under `synth` (one attempt per
 *  symbol, ever) with the accepted definitions inside it. Carry those definitions into `synthEnvs`
 *  (same ids and bodies, so P2–P4 artifacts keyed by obj_id stay valid) and drop the ledger. */
export function migrateSynthLedger(cache: { synth?: Record<string, unknown>; synthEnvs?: Record<string, SynthEnvRecord>; synthRetries?: unknown }): void {
  cache.synthEnvs ??= {};
  const legacy = Object.values(cache.synth ?? {}).filter((v): v is { symbol: string; accepted: boolean; id?: string; title?: string; body?: string } =>
    v !== null && typeof v === "object" && "accepted" in v && "symbol" in v);
  if (legacy.length === 0 && !("synthRetries" in cache)) return;
  for (const e of legacy) {
    if (!e.accepted || !e.id || e.body == null) continue;
    const rec = cache.synthEnvs[e.id] ?? { symbols: [], title: e.title, body: e.body };
    if (!rec.symbols.includes(e.symbol)) rec.symbols.push(e.symbol);
    cache.synthEnvs[e.id] = rec;
  }
  cache.synth = {};
  delete cache.synthRetries;
}

/**
 * P1 — paper plan + frozen formal layer.
 *
 * ONE ORDER: solve explicit prerequisites from the outline's planned `home_objs`; synthesized
 * definitions are inserted before their first use. Persist the result as `objs`, so the reviewer,
 * layer and later stages see the same order without overwriting the next entry's starting point.
 * ONE WRITER: the render prompts (touch-up from NL; theorem/lemma and every repair with a Lean
 * counterpart from Lean) are the only thing that writes a body. TWO JUDGES feed it defects: the
 * codex notation reviewer (does some env define each symbol?) and the Lean-fidelity judge
 * (`judgeStatements`). ONE CACHE: `p1_cache.json` holds content-keyed model outputs and the
 * synthesized definitions; the frozen bodies are persisted onto the graph once, after the loop
 * converges.
 */
export async function stageP1(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p1.stub"), "dry-run\n");
    return;
  }
  const { deps, repoRoot } = io.ctx;
  const graph = io.bank.graph;
  // D-stage narrative layer (UNTRUSTED pre-formalization prose; authoring uses are
  // subordinated to the frozen layer, restriction-shaped fields feed detectors).
  const narrative = await loadBankNarrative(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec);
  const dstageDefinitionContext = [
    narrative.definitionList && `D-stage definition constructions (source of truth for named objects):\n${narrative.definitionList}`,
    narrative.symbolTable && `D-stage symbol table:\n${narrative.symbolTable}`,
  ].filter(Boolean).join("\n\n") || "(none recorded)";
  const nodes = topoOrder(graph, renderedNodes(graph));
  if (nodes.length === 0) throw new Error("P1: graph has no frozen paper-env nodes to render");
  const nodeIds = nodes.map((n) => n.id);
  const refTargetsById = new Map(
    nodes.map((n) => [n.id, new Set(refTargets(graph, n.id).map((t) => t.id))]),
  );
  const citedDepsById = new Map(nodes.map((n) => [n.id, citedDependencies(graph, n.id)] as const));
  const citedPromptFor = (id: string): string => {
    const deps = citedDepsById.get(id) ?? [];
    if (deps.length === 0) return "(none — do not erase any Lean hypothesis)";
    return deps.map((d) =>
      `- ${d.lean.decl_name ?? d.id}: ${d.nl.statement.replace(/\s+/g, " ").trim()} ` +
      `[source ${d.gate?.source ?? "missing"}; source-matched status ${d.review.status}]`,
    ).join("\n");
  };

  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8");
  const bibText = await readFile(join(io.outDir, "references.bib"), "utf8");
  const poolKeys = new Set(parseBib(bibText).map((e) => e.key));
  // Inline-citation key per CITED node: reconcile its `gate.source` slug to the P0-curated
  // bib key (surname ⊂ author AND equal year) so the touch-up render attributes the imported
  // result with `\citet{<key>}` rather than hardcoded author-year text. Graph-only, match-only:
  // a slug with no confident bib match is simply omitted (the render falls back to plain prose).
  const bibIndex = indexBib(bibText);
  const citeKeyById = new Map<string, string>();
  for (const n of graph.nodes) {
    if (!isCitedNode(n)) continue;
    const std = citedStdFromNode(n);
    if (!std) continue;
    const { citeKey } = reconcileCite(std, bibIndex);
    if (poolKeys.has(citeKey)) citeKeyById.set(n.id, citeKey);
  }
  const locatorById = new Map<string, string>();
  const passedCitedChecks = new Set<string>();
  for (const check of io.bank.citedChecks ?? []) {
    if (check.locator && !locatorById.has(check.name)) locatorById.set(check.name, check.locator);
    if (["cited-verified", "cited-verified-attested"].includes(check.check_status)) {
      passedCitedChecks.add(check.name);
    }
  }
  const usedCited = [...new Map(
    [...citedDepsById.values()].flat().map((n) => [n.id, n] as const),
  ).values()];
  const unsafeCited = usedCited.filter((n) => !passedCitedChecks.has(n.id) || !citeKeyById.has(n.id));
  if (unsafeCited.length > 0) {
    throw new Error(
      "P1 citation erasure refused: each hidden cited premise needs a persisted verified/attested " +
      "source-match and a resolvable references.bib key — " +
      unsafeCited.map((n) => `${n.id} (check=${passedCitedChecks.has(n.id)}, bib=${citeKeyById.has(n.id)})`).join(", "),
    );
  }

  // P5 revision is owned by the single holistic reviser. P1 is initial planning
  // only and must not independently reinterpret a prior referee report, so the
  // outline prompt's revision slot always carries the inert first-draft brief.
  const outlineBrief = FIRST_DRAFT_BRIEF;

  const t0 = Date.now();
  const log = (m: string) => console.error(`[causalsmith P1] +${Math.round((Date.now() - t0) / 1000)}s ${m}`);
  log(`graph: ${nodes.length} frozen paper-env nodes → ${nodeIds.join(", ")}`);

  // Content-keyed cache (a re-run only re-pays for changed inputs). Delete the file to force a
  // full re-render; the synthesized definitions live in it too (`synthEnvs`).
  const cachePath = join(io.outDir, "p1_cache.json");
  type RenderHit = { title?: string; body: string };
  const cache: P1Cache = await loadJsonCache(cachePath, { defaults: { render: {}, notation: {}, synth: {}, synthEnvs: {} } });
  migrateSynthLedger(cache);
  const candidates = cache.candidates ??= {};
  const saveCache = () => writeJsonAtomic(cachePath, cache); // why: a crash mid-write must not corrupt the cache (next run would throw on parse).

  // Model + prompt fingerprints: hashing the actual prompt templates into each cache key
  // makes prompt edits self-invalidating. One fingerprint PER CONSUMER (render / notation / synthesis), so editing one prompt does not needlessly cold the others.
  const promptFp = promptFingerprint;
  const modelKeyBase = `${io.ctx.deps.codexModel ?? "unspecified-codex-model"}|${PRESENTATION_PROSE_POLICY_VERSION}`;
  const renderModelKey = `${modelKeyBase}|${await promptFp("p1_touchup", "p1_render_from_lean")}`;
  const notationModelKey = `${MODELS.codexNotationCheck}|${PRESENTATION_PROSE_POLICY_VERSION}|${await promptFp("p1_notation_check")}`; // the model the call actually uses
  const synthModelKey = `${modelKeyBase}|${await promptFp("p1_synthesize_definition")}`;

  // ── Outline (codex): structure + notation table over the mechanical layer. A valid existing
  // outline.md is REUSED (structure must not silently change on a re-run); `validateOutline`
  // guards staleness (missing/duplicate envs or invalid citations → regenerate). An operator
  // can place newly promoted nodes in authored homes without paying for another full plan.
  // Delete outline.md to explicitly request a fresh structure.
  const mechanical = renderMechanicalLayer(nodes);
  const outlineNarrative = [
    narrative.tldr && `TLDR (pre-formalization research summary):\n${narrative.tldr}`,
    narrative.projectJustification && `Project justification:\n${narrative.projectJustification}`,
    narrative.interpretation && `Interpretation:\n${narrative.interpretation}`,
    narrative.honestScope && `Honest scope (claims the research stage itself disclaims):\n${narrative.honestScope}`,
  ].filter(Boolean).join("\n\n") || "(none recorded)";
  const existingOutline = outlineForPlanning(await readFile(join(io.outDir, "outline.md"), "utf8").catch(() => "")).trim();
  let outlineMd: string;
  if (existingOutline && validateOutline(existingOutline, nodeIds, poolKeys).length === 0) {
    outlineMd = existingOutline;
    log("outline: reusing existing valid outline.md (no restructure on re-run)");
  } else {
    log(
      `outline: calling codex…${
        existingOutline ? " (existing outline invalid for current env set — regenerating)" : ""
      }`,
    );
    const baseOutlinePrompt = await presentationPrompt("p1_plan", {
        note_md: io.bank.noteMd,
        contribution_narrative: outlineNarrative,
        related_work_brief: brief,
        frozen_layer_tex: mechanical,
        pool_keys: [...poolKeys].join(", "),
        revision_brief: outlineBrief,
        // why: reruns with a valid existing outline must preserve structure unless a structural P5 brief requested movement.
        prior_outline: existingOutline || "(first draft — no prior structure to preserve)",
      });
    let outlineProblems: string[] = [];
    outlineMd = "";
    for (let attempt = 0; attempt < 2; attempt++) {
      const repair = attempt === 0 ? "" : [
        "\n\nREPAIR THE PREVIOUS OUTLINE. The deterministic validator rejected it for:",
        ...outlineProblems.map((p) => `- ${p}`),
        "Return a complete replacement outline. In particular, every `bib:` key must be copied verbatim from the verified pool above; keys mentioned in the note or related-work brief but absent from that pool do not exist.",
        "\nPrevious rejected outline:\n",
        outlineMd,
      ].join("\n");
      const outlineRes = await deps.runCodex({
        prompt: baseOutlinePrompt + repair,
        cwd: repoRoot,
        reasoningEffort: "medium",
        leanLsp: false,
        webSearch: true,
      });
      outlineMd = unwrapArtifact(outlineRes.stdout, ["markdown", "md"], "outline_md");
      outlineProblems = validateOutline(outlineMd, nodeIds, poolKeys);
      if (outlineProblems.length === 0) break;
      await writeDiagnostic(io.outDir, "outline_rejected.md", outlineMd + "\n");
      log(`outline: rejected attempt ${attempt + 1}/2 — ${outlineProblems.join("; ")}`);
    }
    if (outlineProblems.length > 0) {
      throw new Error(`P1 outline invalid after repair: ${outlineProblems.join("; ")}`);
    }
    await writeFile(join(io.outDir, "outline.md"), outlineMd + "\n", "utf8");
    log("outline: ok");
  }
  const outline: Outline = parseOutline(outlineMd);
  // Placement advisory: an object a MAIN-BODY theorem uses IN ITS STATEMENT must not be defined
  // only in an appendix. Logged loudly, not fatal — a checkpoint reader fixes it in one line.
  {
    const statementUsesOf = (id: string): string[] =>
      graph.edges.filter((e) => e.kind === "statement-uses" && e.from === id).map((e) => e.to);
    const kindOf = (id: string): string | undefined => graph.nodes.find((n) => n.id === id)?.kind;
    for (const m of lintMainBodyDependencies(outline, statementUsesOf, kindOf)) log(`placement: ${m}`);
  }
  const notation = outline.notation;
  // Objects the planner re-kinded to `algorithmv` render as numbered-step procedures: the touchup
  // prompt is told so (`environment: algorithmv`) and the hint joins the render cache key.
  const envHintFor = (id: string): string =>
    outline.envOverrides[id] === "algorithmv" ? "environment: algorithmv" : "";
  const leanDir = join(repoRoot, io.bank.leanSubdir);
  const realizedSymbols = await discoverRealizedSymbols(leanDir);
  const realizedList = realizedSymbols.length > 0
    ? realizedSymbols.map((s) => `- ${s}`).join("\n")
    : "(none — this paper has no @realizes-tagged symbols)";
  if (realizedSymbols.length > 0) log(`notation: ${realizedSymbols.length} Lean-realized symbol(s) listed for the reviewer`);

  // Titles are carried in a side-map (the render emits them; the loop tracks only bodies).
  const titleById = new Map<string, string>();
  const graphNodeIds = new Set(nodes.map((n) => n.id));
  // A previously approved body is a reusable candidate, not an exemption from new defects.
  // All candidates share the same loop; graph freezes are replaced only after convergence.
  const envForNodeWithOverride = (n: Parameters<typeof envForNode>[0]) =>
    (outline.envOverrides[n.id] as ReturnType<typeof envForNode>) ?? envForNode(n);
  const sourceKeyById = new Map(nodes.map((n) => [n.id, hashEnvBody(JSON.stringify([
    n.nl.statement, n.nl.frozen_body ?? null, n.nl.frozen_title ?? null,
    envForNodeWithOverride(n), n.delivery ?? null, n.lean,
    [...(refTargetsById.get(n.id) ?? [])].sort(),
  ]))]));
  const candidateById = new Map<string, RenderHit>();
  if (!io.ctx.refreshFrozenBodies) {
    for (const n of nodes) {
      const pointer = candidates[n.id];
      const hit = pointer && pointer.sourceKey === sourceKeyById.get(n.id) ? cache.render[pointer.renderKey] : undefined;
      if (typeof hit?.body === "string" && hit.body.trim() && n.delivery?.status !== "undelivered") candidateById.set(n.id, hit);
    }
  }
  const reusableBody = (n: typeof nodes[number]) => candidateById.get(n.id)?.body ?? n.nl.frozen_body;
  const reusableNodes = nodes.filter((n) => reusableBody(n) && !io.ctx.refreshFrozenBodies &&
    n.delivery?.status !== "undelivered" &&
    !(outline.envOverrides[n.id] === "algorithmv" && !isSteppedBodyForTest(reusableBody(n)!)));
  const reusableIds = new Set(reusableNodes.map((n) => n.id));
  for (const n of reusableNodes) {
    const title = candidateById.get(n.id)?.title ?? n.nl.frozen_title;
    if (title != null) titleById.set(n.id, title);
  }
  log(`reuse: ${reusableIds.size} bodies (${candidateById.size} interrupted candidates); current reviewers gate every candidate`);

  // Lean-aware rendering: a theorem/lemma's PAPER statement is rendered DIRECTLY from its
  // machine-verified Lean signature (complete + curated), not from a possibly-loose NL headline.
  // Definitions/assumptions keep the NL render on the first pass; a Lean-fidelity defect on ANY
  // env is repaired from the Lean counterpart the judge resolved (`auditContextById`).
  const kindById = new Map(nodes.map((n) => [n.id, n.kind] as const));
  const leanIndex = await buildLeanContextIndex(repoRoot, io.bank.leanSubdir);
  const leanCtxById = new Map<string, LeanContext>();
  for (const n of nodes) {
    if ((n.kind === "theorem" || n.kind === "lemma") && n.lean.decl_name && n.lean.file) {
      const ctx = await leanIndex.contextFor({ decl_name: n.lean.decl_name, file: n.lean.file });
      if (ctx) leanCtxById.set(n.id, ctx);
    }
  }
  if (leanCtxById.size > 0) log(`Lean-aware render: ${leanCtxById.size} theorem/lemma statement(s) will render from Lean`);
  const auditContextById = new Map<string, StatementLeanContext>();
  // Lean-first synthesis: a symbol the Lean already defines (an `@realizes` tag or a same-named
  // def-like declaration) is never written from usage — its definition renders from that
  // declaration and carries the link.
  const symbolClusters = await buildSymbolClusters(leanDir, realizedSymbols.map((name) => ({ name })));
  const moduleDecls = await buildModuleDeclIndex(repoRoot, io.bank.leanSubdir);
  // Declarations a paper environment already presents: a symbol they define under other notation
  // is a use to fix, never a second definition.
  const presentedDecls = new Set(
    [...nodes, ...graph.nodes.filter(isCitedNode)].flatMap((n) => n.lean.decl_name ? [n.lean.decl_name] : []),
  );
  const resolveHomes = (symbols: readonly string[]) => resolveSymbolHomes(symbols, symbolClusters, moduleDecls, presentedDecls);

  // The semantic reviewer treats `D_{G_i t}` and `D_{G_i,t}` as distinct notation; keep the graph's
  // comma-free cohort-time convention for synthesized definitions. Also restore a `\t` the JSON
  // parse turned into a tab (`\to` → TAB + `o`).
  const normalizeSynthNotation = (body: string): string =>
    body
      .replace(/\t(?=[A-Za-z])/g, "\\t")
      .replace(/D_\{G_i,\s*t\}/g, "D_{G_i t}");

  // ── Synthesized definitions (durable in cache.synthEnvs). Ids are never reused: the counter is
  // fixed before any release, so a released definition's id stays retired (downstream notes may
  // name it).
  let synthCount = Math.max(cache.synthCounter ?? 0, ...Object.keys(cache.synthEnvs).map((id) => Number(id.slice("synth_".length))).filter(Number.isFinite));
  cache.synthCounter = synthCount;
  const nextSynthId = (): string => {
    cache.synthCounter = ++synthCount;
    return `synth_${synthCount}`;
  };
  const released = releaseLeanResolvableSynths(cache, (symbols) => resolveHomes(symbols).homes.length > 0);
  if (released.length > 0) {
    log(`synthesis: released ${released.length} cached presentation-only definition(s) whose symbols the Lean defines — ${released.join(", ")}`);
    io.state.notes.push(`P1: released presentation-only definition(s) ${released.join(", ")} — their symbols are defined in Lean and re-render from it`);
    await saveCache();
  }
  const symbolsBySynthId = new Map<string, string[]>();
  for (const [id, rec] of Object.entries(cache.synthEnvs)) {
    if (rec.lean) {
      const ctx = await leanIndex.contextFor({ decl_name: rec.lean.decl, file: rec.lean.file });
      if (!ctx) {
        // The declaration was renamed or deleted: release the definition; its symbols re-resolve.
        delete cache.synthEnvs[id];
        io.state.notes.push(`P1: released definition ${id} — its Lean declaration ${rec.lean.decl} (${rec.lean.file}) no longer exists; ${rec.symbols.join(", ")} re-resolve`);
        await saveCache();
        continue;
      }
      kindById.set(id, "definition");
      leanCtxById.set(id, ctx);
    }
    symbolsBySynthId.set(id, rec.symbols);
    if (rec.title) titleById.set(id, rec.title);
  }
  const synthEnv = (id: string): P1Env => {
    const body = normalizeSynthNotation(cache.synthEnvs[id].body);
    return { id, env: "definitionv", statement: body, body, refSet: [] };
  };

  // ── Order (the ONE order): outline paper order + synth insertion + definition-order repair.
  const assembleTex = (envs: readonly P1Env[]): string =>
    [
      "% Frozen formal layer — causalsmith P1 (graph render). Bodies are hash-pinned; do not edit.",
      ...envs.flatMap((e) => {
        const t = titleById.get(e.id);
        return [`\\begin{${e.env}}{${e.id}}${t ? `[${t}]` : ""}`, e.body, `\\end{${e.env}}`, ""];
      }),
    ].join("\n");
  const orphanSynths = new Set<string>(); // synthesized definitions with no visible user, per the latest ordering
  const orderEnvs = (envs: readonly P1Env[]): { ordered: P1Env[]; problems: LintProblem[] } => {
    const all = [...envs];
    const graphEnvs = paperOrder(outline, all.filter((e) => !isSynthId(e.id)));
    orphanSynths.clear();
    const withSynths = insertSynths(graphEnvs, all.filter((e) => isSynthId(e.id)), symbolsBySynthId, titleById, orphanSynths);
    const { envs: ordered, problems } = repairDefinitionOrder(withSynths, refTargetsById, titleById, symbolsBySynthId);
    return { ordered, problems };
  };
  const assemble = (envs: P1Env[]): string => assembleTex(orderEnvs(envs).ordered);

  /** Parse the delimiter-based render output (robust to multi-line LaTeX, which a JSON container
   *  mangles). Format per env: `@@@ENV <obj_id>@@@\nTITLE: <title>\n@@@BODY@@@\n<body…>\n@@@END@@@`. */
  const parseRender = (text: string): Map<string, RenderHit> => {
    const out = new Map<string, RenderHit>();
    const re = /@@@ENV\s+(\S+?)@@@\s*\n(?:TITLE:\s*(.*)\n)?@@@BODY@@@\s*\n([\s\S]*?)\n?@@@END@@@/g;
    let m: RegExpExecArray | null;
    while ((m = re.exec(text))) {
      const body = m[3].trim();
      if (body !== "") out.set(m[1].trim(), { title: m[2]?.trim() || undefined, body });
    }
    return out;
  };

  const BATCH = 6;
  type RenderReq = { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: P1Env["delivery"] };
  const enforceUndeliveredDisclosure = (r: RenderReq, body: string): string => {
    if (r.delivery?.status !== "undelivered") return body;
    const framed = undeliveredRemarkBody(r.statement, r.delivery.reason, body);
    if (framed !== body.trim()) titleById.set(r.id, "Open direction");
    return framed;
  };
  const renderBatch = async (reqs: RenderReq[]): Promise<Map<string, RenderHit>> => {
    const res = await deps.runCodex({
      prompt: await presentationPrompt("p1_touchup", {
        notation_table: notation,
        envs_block: reqs
          .map((r) => p1TouchupEnvInput({
            ...r,
            citedDependencies: citedPromptFor(r.id),
            environmentHint: envHintFor(r.id),
          }))
          .join("\n\n"),
      }),
      cwd: repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
    });
    const parsed = parseRender(res.stdout);
    if (parsed.size < reqs.length) {
      await writeDiagnostic(io.outDir, "p1_render_raw.txt", res.stdout.slice(0, 20000));
    }
    return parsed;
  };
  type LeanRenderCtx = Pick<LeanContext, "statement" | "referencedDefs">;
  /** The Lean counterpart a render of `r` is written from: the decl-based context for a theorem/
   *  lemma first render; the judge's resolved context for any defect-driven repair. */
  const leanCtxFor = (r: RenderReq): LeanRenderCtx | undefined => {
    if (r.defects) {
      const a = auditContextById.get(r.id);
      if (a) return { statement: a.leanStatement, referencedDefs: a.refDefs };
    }
    return leanCtxById.get(r.id);
  };
  const renderKey = (r: RenderReq) => renderCacheKey(renderModelKey, r, citedPromptFor(r.id), envHintFor(r.id));
  const leanKey = (r: RenderReq, ctx: LeanRenderCtx): string =>
    leanRenderCacheKey(
      renderModelKey,
      r,
      { statement: ctx.statement, referencedDefs: ctx.referencedDefs || "(none indexed — the statement references no local definitions)" },
      kindById.get(r.id) ?? "theorem",
      citedPromptFor(r.id),
    );
  /** Render one statement from its Lean counterpart. Output is the same `@@@ENV/TITLE/BODY` envelope
   *  the NL render uses, so `parseRender` handles both. */
  const renderFromLean = async (r: RenderReq, ctx: LeanRenderCtx): Promise<RenderHit | null> => {
    const res = await deps.runCodex({
      prompt: await presentationPrompt("p1_render_from_lean", {
        obj_id: r.id,
        kind: kindById.get(r.id) ?? "theorem",
        lean_statement: ctx.statement,
        referenced_defs: ctx.referencedDefs || "(none indexed — the statement references no local definitions)",
        nl_statement: r.statement,
        ref_set: r.refSet.join(", ") || "(none)",
        cited_dependencies: citedPromptFor(r.id),
        notation_table: notation,
        prior_and_defects: r.defects ? `prior_body: ${r.priorBody ?? ""}\ndefects: ${r.defects.join(" | ")}` : "(first render — none)",
      }),
      cwd: repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
    });
    const hit = parseRender(res.stdout).get(r.id);
    if (!hit) await writeDiagnostic(io.outDir, "p1_render_from_lean_raw.txt", res.stdout.slice(0, 20000));
    return hit ?? null;
  };

  const render: P1LoopHooks["render"] = async (reqs) => {
    reqs = reqs.map((r) => r.defects ? { ...r, refSet: [...new Set([...r.refSet, ...latestEnvs.map((e) => e.id)])].filter((id) => id !== r.id) } : r);
    const out = new Map<string, string>();
    // Canonical cross-references on every body the loop sees (cache hits included): a dropped kind
    // prefix is repaired here, deterministically, so only a genuinely unresolvable target reaches
    // the reviewer's dangling-reference finding and costs a render round.
    const canonicalOut = (): Map<string, string> => {
      const knownIds = new Set([...graphNodeIds, ...Object.keys(cache.synthEnvs)]);
      return new Map([...out].map(([id, body]) => [id, repairObjRefs(normalizeCrefs(body), knownIds).tex]));
    };
    const keyById = new Map<string, string>();
    const acceptHit = (r: RenderReq, hit: RenderHit, store: boolean): void => {
      out.set(r.id, isSynthId(r.id) ? normalizeSynthNotation(hit.body) : enforceUndeliveredDisclosure(r, hit.body));
      if (hit.title) titleById.set(r.id, hit.title);
      if (store) cache.render[keyById.get(r.id)!] = hit;
      const sourceKey = sourceKeyById.get(r.id);
      if (sourceKey) candidates[r.id] = { sourceKey, renderKey: keyById.get(r.id)! };
      // A re-rendered synthesized definition updates its durable record, so a re-run recovers
      // the repaired definition, not the flagged one.
      if (isSynthId(r.id) && cache.synthEnvs[r.id]) {
        cache.synthEnvs[r.id] = { ...cache.synthEnvs[r.id], body: normalizeSynthNotation(hit.body), title: hit.title ?? cache.synthEnvs[r.id].title };
      }
    };
    const leanMiss: { r: RenderReq; ctx: LeanRenderCtx }[] = [];
    const nlMiss: RenderReq[] = [];
    for (const r of reqs) {
      const ctx = leanCtxFor(r);
      const useLean = shouldUseLeanRender(r.delivery?.status, ctx !== undefined);
      const k = useLean ? leanKey(r, ctx!) : renderKey(r);
      keyById.set(r.id, k);
      // Prior body and defects are key inputs: an identical interrupted request can reuse its
      // output; a new finding against the changed body gets a different key and a fresh repair.
      const hit = cache.render[k];
      if (hit) acceptHit(r, hit, false);
      else if (useLean) leanMiss.push({ r, ctx: ctx! });
      else nlMiss.push(r);
    }
    const total = leanMiss.length + nlMiss.length;
    if (total === 0) {
      log(`render: all ${reqs.length} env(s) cached`);
      await saveCache();
      return canonicalOut();
    }
    log(`render: ${reqs.length - total} cached, ${leanMiss.length} from Lean + ${nlMiss.length} from NL via codex${reqs[0]?.defects ? " (re-render)" : ""}…`);
    // Persist each successful job before its siblings can fail. mapLimit drains in-flight work;
    // the final flush below retains the newest complete cache snapshot on every exit.
    const leanFallback: RenderReq[] = [];
    try {
      await mapLimit(leanMiss, 4, async ({ r, ctx }) => {
        const hit = await renderFromLean(r, ctx);
        if (hit) { acceptHit(r, hit, true); await saveCache(); }
        else leanFallback.push(r);
      });
      const nlAll = [...nlMiss, ...leanFallback];
      const chunks: RenderReq[][] = [];
      for (let i = 0; i < nlAll.length; i += BATCH) chunks.push(nlAll.slice(i, i + BATCH));
      await mapLimit(chunks, 4, async (chunk) => {
        const rendered = await renderBatch(chunk);
        for (const r of chunk) {
          const hit = rendered.get(r.id);
          if (hit) acceptHit(r, hit, true);
        }
        await saveCache();
      });
      // Recover omitted envelopes once, without discarding successful siblings.
      const missing = nlAll.filter((r) => !out.has(r.id));
      if (missing.length > 0) {
        log(`render: targeted retry for ${missing.length} omitted env(s) — ${missing.map((r) => r.id).join(", ")}`);
        await mapLimit(missing, 4, async (r) => {
          const hit = (await renderBatch([r])).get(r.id);
          if (hit) { acceptHit(r, hit, true); await saveCache(); }
        });
      }
    } finally {
      await saveCache();
    }
    log(`render: ${out.size}/${reqs.length} bodies`);
    return canonicalOut();
  };

  // The most recent env set the review hook saw — the synthesize hook's evidence base for usage
  // excerpts (the loop always reviews before it synthesizes).
  let latestEnvs: P1Env[] = [];
  /** One cached call to the notation reviewer. Raw problems are cached by layer content; routing is
   *  recomputed on every read so the routing policy applies to cached reviews too. */
  const reviewNotation = async (layer: string): Promise<NotationReviewerProblem[]> => {
    const layerKey = hashEnvBody(`${notationModelKey}§${layer}§${notation}§${realizedList}`);
    if (Object.hasOwn(cache.notation, layerKey)) return cache.notation[layerKey];
    const prompt = await presentationPrompt("p1_notation_check", {
      frozen_layer: layer,
      notation_table: notation,
      lean_realized_symbols: realizedList,
    });
    // An unusable reply is a mechanical failure: retried once at the call site, then thrown.
    let problems: NotationReviewerProblem[] | null = null;
    for (let attempt = 0; attempt < 2 && problems === null; attempt++) {
      const res = await deps.runCodex({ model: MODELS.codexNotationCheck, prompt, cwd: repoRoot, reasoningEffort: "medium", leanLsp: false, outputSchema: NOTATION_REPLY });
      try {
        problems = parseNotationReviewerOutput(res.stdout);
      } catch (e) {
        await writeDiagnostic(io.outDir, "p1_notation_check_raw.txt", res.stdout.slice(0, 20000));
        if (attempt === 1) throw e;
      }
    }
    cache.notation[layerKey] = problems!;
    await saveCache();
    return problems!;
  };
  /** Blocks for the judge and the layer: graph blocks from `blocksFromGraph` (env overrides, cited
   *  dependencies) plus one presentation-synthesized block per synth, in the given order. */
  const blocksFor = (ordered: readonly P1Env[]): FormalBlock[] => {
    const bodyById = new Map(ordered.map((e) => [e.id, e.body] as const));
    const bodies = new Map(nodes.map((n) => [
      n.id,
      normalizeCrefs(bodyById.get(n.id) ?? ""),
    ] as const));
    const graphBlocks = blocksFromGraph(graph, bodies, titleById, outline.envOverrides, log, { citeKeyByNodeId: citeKeyById, locatorByNodeId: locatorById });
    const synthBlocks: FormalBlock[] = ordered.filter((e) => isSynthId(e.id)).map((e) => {
      const lean = cache.synthEnvs[e.id]?.lean ?? null;
      return {
        obj_id: e.id,
        alias: null,
        kind: "definition",
        env: "definitionv",
        title: titleById.get(e.id) ?? null,
        body: e.body,
        ref_set: [],
        lean,
        status: lean ? "matched" : "presentation-synthesized",
        provenance: "presentation-synthesized",
        cited_dependencies: [],
      };
    });
    const blockById = new Map([...graphBlocks, ...synthBlocks].map((b) => [b.obj_id, b] as const));
    return ordered.flatMap((e) => blockById.get(e.id) ?? []);
  };
  const judgeMemo = new Map<string, StatementJudgement>();
  let lastVerdicts = new Map<string, StatementJudgement>();
  const review: P1LoopHooks["review"] = async (layer, envs) => {
    latestEnvs = envs;
    log("review: lints + codex notation + Lean judge…");
    // Order is solved, never judged: what the solve could not order (a definition cycle, a
    // result named as a home) is an advisory that rides along with the round's findings.
    const { ordered, problems: orderProblems } = orderEnvs(envs);
    const known = new Set(envs.map((e) => e.id));
    // Let both reviewers finish saving their receipts before exposing either failure.
    const [notationResult, judgeResult] = await Promise.allSettled([
      reviewNotation(layer),
      judgeStatements(io, blocksFor(ordered), judgeMemo),
    ]);
    if (notationResult.status === "rejected") throw notationResult.reason;
    if (judgeResult.status === "rejected") throw judgeResult.reason;
    const notationProblems = notationResult.value;
    const judged = judgeResult.value;
    for (const [id, ctx] of judged.contexts) auditContextById.set(id, ctx);
    lastVerdicts = judged.verdicts;
    const findings: P1Finding[] = [
      ...[
        ...lintAnchors(layer, known, null),
        ...lintClarity(layer),
        ...lintSelfContainment(layer),
        ...lintCrossRefs(layer, refTargetsById, known),
        ...lintReferences(layer),
        ...lintHypothesisPresentation(layer),
      ].map(toFinding),
      ...routeNotationProblems(notationProblems, {
        knownIds: known,
        definitionFor: (symbol) => {
          const synth = [...symbolsBySynthId].find(([, symbols]) =>
            symbols.some((s) => containsNotation(symbol, s) && containsNotation(s, symbol)));
          if (synth) return synth[0];
          const decl = resolveHomes([symbol]).presentedBy.get(symbol);
          return decl ? nodes.find((n) => n.lean.decl_name === decl)?.id : undefined;
        },
      }),
    ];
    for (const [id, v] of judged.verdicts) {
      if (v.verdict === "faithful") continue;
      if (v.verdict === "missing-coverage") {
        findings.push({ gate: "lean-coverage", objId: id, fixLocus: "halt",
          detail: `Lean component mapping needs correction; preserve the statement: ${v.detail ?? "a supporting declaration is missing from the mapped pieces"}` });
        continue;
      }
      findings.push({ gate: "lean-drift", objId: id, fixLocus: "wording-revise",
        detail: `Lean fidelity: ${v.detail ?? "the body disagrees with the Lean statement"}` });
    }
    findings.push(...orderProblems.map(toFinding)); // the tolerated-shape advisories
    return findings;
  };

  /** The definition of `home.symbols`, rendered from the Lean declaration that defines them and
   *  linked to it (the judge audits it against that declaration like any Lean-backed env). A
   *  declaration an earlier definition already links takes the new symbols into that definition. */
  const defineFromLean = async (home: SymbolLeanHome): Promise<P1Env> => {
    const ctx = await leanIndex.contextFor({ decl_name: home.decl, file: home.file, line: home.line });
    if (!ctx) throw new Error(`P1: Lean declaration ${home.decl} (${home.file}) defines ${home.symbols.join(", ")} but its source could not be read`);
    const existing = Object.entries(cache.synthEnvs).find(([, rec]) => rec.lean?.decl === home.decl)?.[0];
    const id = existing ?? nextSynthId();
    const symbols = [...new Set([...(cache.synthEnvs[id]?.symbols ?? []), ...home.symbols])];
    kindById.set(id, "definition");
    leanCtxById.set(id, ctx);
    const req: RenderReq = {
      id,
      statement: `Definition of the paper symbol(s) ${symbols.join(", ")} — introduce exactly these symbols, spelled as the statements write them.`,
      refSet: [],
    };
    const key = leanKey(req, ctx);
    const hit = cache.render[key] ?? (await renderFromLean(req, ctx)) ?? (await renderFromLean(req, ctx));
    if (!hit) throw new Error(`P1: rendering the definition of ${symbols.join(", ")} from Lean ${home.decl} failed twice — see logs/p1_render_from_lean_raw.txt and re-run P1`);
    cache.render[key] = hit;
    cache.synthEnvs[id] = { symbols, title: hit.title, body: normalizeSynthNotation(hit.body), lean: { decl: home.decl, file: home.file } };
    symbolsBySynthId.set(id, symbols);
    if (hit.title) titleById.set(id, hit.title);
    io.state.notes.push(`P1: definition ${id} for ${home.symbols.join(", ")} rendered from Lean ${home.decl} (${home.file})`);
    await saveCache();
    return synthEnv(id);
  };

  const synthesize: P1LoopHooks["synthesize"] = async (symbols, findings) => {
    // Existing providers are repaired by the router. Keep a final duplicate guard for grouped
    // requests: an unhandled symbol remains unresolved, never implicitly approved.
    const coveredSymbols = [...symbolsBySynthId.values()].flat();
    const isCovered = (x: string) => coveredSymbols.some((c) => containsNotation(x, c) && containsNotation(c, x));
    const [already, fresh] = [...new Set(symbols)].reduce<[string[], string[]]>(
      ([a, f], x) => (isCovered(x) ? [[...a, x], f] : [a, [...f, x]]), [[], []]);
    if (already.length > 0) {
      io.state.notes.push(`P1: reviewer re-requested ${already.join(", ")} although a synthesized definition already covers it — existing definition requires repair`);
    }
    // Lean first: symbols a Lean declaration already defines render from it (one definition per
    // declaration — a structure defines all of its fields' symbols together); a declaration an
    // earlier definition already links gains the new symbols and re-renders. Only the symbols no
    // declaration covers go to the definition writer.
    const { homes, unresolved: leanless, presentedBy } = resolveHomes(fresh);
    const envs: P1Env[] = [];
    for (const home of homes) envs.push(await defineFromLean(home));
    for (const [symbol, decl] of presentedBy) {
      const env = nodes.find((n) => n.lean.decl_name === decl)?.id ?? decl;
      io.state.notes.push(`P1: ${symbol} is defined by ${env} (Lean ${decl}) under other notation — the using env should write that notation; its using environment requires repair`);
      already.push(symbol);
    }
    const requested = leanless.filter((x) => !presentedBy.has(x)).slice(0, 8);
    if (requested.length === 0) return { envs, unresolved: already };
    const usagesFor = (symbol: string) => {
      const requests = findings.filter((f) => f.symbol && atomicRequestedNotationSymbols(f.symbol).includes(symbol));
      const users = new Set(requests.flatMap((f) => f.usedIn ?? []));
      const usageEnvs = latestEnvs
        .filter((e) => users.has(e.id) || containsNotation(`${titleById.get(e.id) ?? ""} ${e.body}`, symbol))
        .slice(0, 3);
      return [...requests.map((f) => `  Defect: ${f.detail}`),
        ...usageEnvs.map((e) => `  - ${e.id}: ${e.body.replace(/\s+/g, " ").slice(0, 600)}`)].join("\n");
    };
    // ONE batched call per request: the writer groups the symbols of a single object family into one
    // definition (journal style) instead of minting a micro-definition per symbol.
    const symbolsBlock = requested.map((symbol) => `SYMBOL: ${symbol}\n${usagesFor(symbol)}`).join("\n\n");
    const key = hashEnvBody([synthModelKey, symbolsBlock, dstageDefinitionContext].join("§"));
    if (!Object.hasOwn(cache.synth, key)) {
      const prompt = await presentationPrompt("p1_synthesize_definition", {
        symbols_block: symbolsBlock,
        dstage_constructions: dstageDefinitionContext,
        note_md: io.bank.noteMd,
        lean_subdir: io.bank.leanSubdir,
      });
      let groups: SynthGroup[] | null = null;
      for (let attempt = 0; attempt < 2 && groups === null; attempt++) {
        const res = await deps.runCodex({ prompt, cwd: repoRoot, reasoningEffort: "medium", leanLsp: true });
        // A reply without well-formed delimited blocks is a mechanical failure — retried once, then thrown.
        const parsed = parseSynthReply(res.stdout);
        if (parsed) {
          groups = parsed;
        } else {
          await writeDiagnostic(io.outDir, "p1_synthesize_raw.txt", res.stdout.slice(0, 20000));
        }
      }
      if (groups === null) throw new Error(`P1 synthesis reply unparseable twice for ${requested.join(", ")} — see logs/p1_synthesize_raw.txt and re-run P1`);
      const norm = (s: string) => s.replace(/\s+/g, "");
      const requestedByKey = new Map(requested.map((s) => [norm(s), s] as const));
      const ids: (string | null)[] = groups.map((g) => {
        const covered = [...new Set(g.symbols.map((x) => requestedByKey.get(norm(x))).filter((x): x is string => x !== undefined))];
        // Reject labels and STRUCTURAL environments, but keep subsidiary math environments:
        // `cases`/`aligned`/matrices are the natural body of a piecewise class definition.
        const structuralEnv = [...g.body.matchAll(/\\(?:begin|end)\{([A-Za-z]+)\*?\}/g)].some(
          (m) => !/^(?:cases|dcases|aligned|alignedat|gathered|split|array|[pbBvV]?matrix|smallmatrix)$/.test(m[1]),
        );
        if (covered.length === 0 || !g.body.trim() || structuralEnv || /\\label\b/.test(g.body)) {
          if (covered.length > 0) io.state.notes.push(`P1: synthesis for ${covered.join(", ")} rejected (structural env/label/empty) — remains unresolved`);
          else if (g.symbols.length > 0) io.state.notes.push(`P1: synthesis group dropped — echoed symbol(s) ${g.symbols.join(", ")} match no requested symbol`);
          return null;
        }
        const id = nextSynthId();
        cache.synthEnvs[id] = { symbols: covered, title: g.title, body: normalizeSynthNotation(g.body.trim()) };
        io.state.notes.push(`P1: synthesized definition ${id} for orphan symbol(s) ${covered.join(", ")}`);
        return id;
      });
      cache.synth[key] = { groups, ids };
      await saveCache();
    }
    for (const id of cache.synth[key].ids) {
      if (id === null || !cache.synthEnvs[id]) continue;
      symbolsBySynthId.set(id, cache.synthEnvs[id].symbols);
      if (cache.synthEnvs[id].title) titleById.set(id, cache.synthEnvs[id].title!);
      envs.push(synthEnv(id));
    }
    const coveredNow = new Set(envs.flatMap((e) => symbolsBySynthId.get(e.id) ?? []));
    const unresolved = [...already, ...requested.filter((s) => !coveredNow.has(s))];
    if (unresolved.length > 0) {
      io.state.notes.push(`P1: synthesis left ${unresolved.join(", ")} undefined (rejected or judged not faithfully definable) — remains unresolved`);
    }
    return { envs, unresolved };
  };

  // All bodies share the same repair loop; only candidates without a reusable body render first.
  const recoveredSynth = Object.keys(cache.synthEnvs).map(synthEnv);
  if (recoveredSynth.length > 0) log(`resume: recovered ${recoveredSynth.length} synthesized definition(s) from the cache`);
  const initialEnvs: P1Env[] = nodes.map((n) => ({
    id: n.id,
    env: envForNodeWithOverride(n)!,
    statement: n.nl.statement,
    // The same canonical references the loop applies to rendered bodies, so an interrupted
    // candidate re-enters as the loop left it rather than paying a wording round for a ref repair.
    body: repairObjRefs(normalizeCrefs(reusableIds.has(n.id) ? reusableBody(n)! : n.nl.statement), new Set([...graphNodeIds, ...Object.keys(cache.synthEnvs)])).tex,
    refSet: [...(refTargetsById.get(n.id) ?? [])],
    ...(n.delivery?.status === "undelivered"
      ? { delivery: { status: "undelivered" as const, role: n.delivery.role, reason: n.delivery.reason ?? "the item is outside the delivered theorem inventory" } }
      : {}),
  }));
  const formalLayerPath = join(io.outDir, "formal_layer.tex");
  const onRound: P1LoopHooks["onRound"] = async ({ phase, iter, envs, findings }) => {
    // Always persist the latest layer so a slow/timed-out run leaves the render on disk.
    await writeFile(formalLayerPath, assemble(envs) + "\n", "utf8");
    if (phase === "render0") log(`render0: persisted ${envs.length}-env layer to formal_layer.tex`);
    else {
      const blocking = (findings ?? []).filter((f) => !isAdvisoryFinding(f));
      log(`review iter ${iter}: ${findings?.length ?? 0} finding(s) (${blocking.length} actionable) — ${[...new Set(blocking.map((f) => f.gate))].join(", ") || "clean"}`);
    }
  };
  // notation_review.json is written on EVERY exit path (success, non-convergence, mid-loop throw)
  // so a failed re-run can never leave a prior converged run's `ok: true` file on disk.
  const dedupeAdvisories = (fs: P1Finding[]): P1Finding[] => {
    const seen = new Set<string>();
    return fs.filter((f) => {
      const key = `${f.gate}|${f.objId ?? ""}|${f.detail}`;
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  };
  const writeNotationReview = (ok: boolean, advisories: P1Finding[], iterations: number) =>
    writeJsonAtomic(join(io.outDir, "notation_review.json"), {
      ok,
      iterations,
      advisories: dedupeAdvisories(advisories),
      synthesized: cache.synthEnvs,
    });

  let result;
  try {
    result = await runP1Loop(
      [...recoveredSynth, ...initialEnvs],
      { render, review, synthesize, assemble, onRound, maxIterations: 6 },
      { renderIds: initialEnvs.filter((e) => !reusableIds.has(e.id)).map((e) => e.id) },
    );
  } catch (e) {
    await writeNotationReview(false, [], 0).catch(() => undefined); // why: best-effort — the loop error is the primary signal.
    throw e;
  }
  log(`loop: ${result.ok ? "converged" : "did NOT converge"} in ${result.iterations} iter(s); ${result.advisories.length} advisory`);
  if (!result.ok) {
    io.state.hard_gate_failures = result.unresolved.map((f) => ({ gate: f.gate, objId: f.objId, detail: f.detail }));
    await writeNotationReview(false, result.advisories, result.iterations);
    throw new Error(
      `P1 loop did not converge in ${result.iterations} iterations (latest layer persisted to formal_layer.tex; ` +
        `renders/reviews/synthesis/verdicts are cached — fix the blocking input and re-run): ` +
        result.unresolved.map((f) => `[${f.gate}] ${f.objId ?? ""} ${f.detail}`).join("; "),
    );
  }

  // ── Converged: persist the resolved layout and retain the planner homes for the next solve.
  // A halt an earlier attempt recorded
  // is stale now.
  io.state.hard_gate_failures = [];
  const { ordered } = orderEnvs(result.envs);
  if (orphanSynths.size > 0) {
    const note = `P1: ${orphanSynths.size} synthesized definition(s) have no visible user and were placed at the end of the setup: ${[...orphanSynths].sort().join(", ")} — excise each from outline.md, or fix the symbol spelling at its use site, then --from P1 (affected sections re-draft).`;
    if (!io.state.notes.includes(note)) io.state.notes.push(note);
  }
  const blocks = blocksFor(ordered);
  const homes = new Map(outline.sections.map((s) => [s.name, s.objs.filter((id) => !isSynthId(id))]));
  await writeTextAtomic(join(io.outDir, "outline.md"), rewriteOutlineObjs(outlineMd, sectionObjs(outline, ordered), homes) + "\n");
  // Atomic like outline.md: a kill mid-write must not leave a truncated layer for P2 to reject.
  await writeTextAtomic(join(io.outDir, "formal_layer.json"), JSON.stringify(FormalLayerSource.parse({ commit: null, blocks }), null, 2) + "\n");
  await writeTextAtomic(formalLayerPath, "% DERIVED from formal_layer.json — read-only, do not edit.\n" + blocksToTex(blocks) + "\n");
  await saveCache();
  // Freeze the judge-faithful graph bodies ONCE, on the layer both judges accepted (the final review
  // saw exactly these bodies: convergence means it returned nothing actionable).
  const faithful = new Map<string, { body: string; title: string | null }>();
  for (const e of ordered) {
    if (!graphNodeIds.has(e.id)) continue;
    if (lastVerdicts.get(e.id)?.verdict === "faithful") faithful.set(e.id, { body: e.body, title: titleById.get(e.id) ?? null });
  }
  const frozen = await persistFrozenBodies(io, faithful);
  log(`Lean judge: all judged envs faithful${frozen > 0 ? ` (${frozen} body/bodies frozen onto the graph)` : ""}`);

  // Ordering and optional cross-reference advisories remain visible at the checkpoint.
  const advisories = dedupeAdvisories(result.advisories);
  if (advisories.length > 0) {
    // The full list is in notation_review.json; the state note carries the count by gate and
    // the first few, not a page of text.
    const byGate = [...advisories.reduce((m, f) => m.set(f.gate, (m.get(f.gate) ?? 0) + 1), new Map<string, number>())]
      .map(([g, n]) => `${g} ×${n}`).join(", ");
    const shown = advisories.slice(0, 8).map((f) => f.detail.slice(0, 200));
    io.state.notes.push(
      `P1 advisories (${advisories.length}: ${byGate}; full list in notation_review.json): ` +
        shown.join("; ") + (advisories.length > shown.length ? `; … +${advisories.length - shown.length} more` : ""),
    );
  }
  await writeNotationReview(true, advisories, result.iterations);
}
