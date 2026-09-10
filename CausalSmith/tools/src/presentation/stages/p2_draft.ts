import { readFile, writeFile, mkdir } from "node:fs/promises";
import { PROOF_AUDIT_FAILURE_MARKER, PROOF_AUDIT_RENDERING_MARKER } from "../promotion.js";
import { join } from "node:path";
import { extractBalancedEnv, stripTexComments } from "../../shared/tex_text.js";
import type { StageIO } from "../pipeline.js";
import { PRESENTATION_PROSE_POLICY_VERSION, presentationPrompt } from "../prompt_io.js";
import { notationForArtifact, parseOutline, unwrapArtifact, type Outline } from "../stage_util.js";
import {
  canonicalizeProofTitle,
  readOptionalTitle,
  lintAnchors,
  lintEnvOrder,
  stripRedundantEnvLabels,
  normalizeFrozenEnvs,
  parseAnchoredEnvs,
  repairObjRefs,
  lintReferences,
  normalizeCrefs,
  placeFrozenEnvs,
  hashEnvBody,
  type AnchoredEnv,
  type LintProblem,
} from "../tex_anchors.js";
import { FormalLayerSource, normalizeCitedScopeFootnotes, texEnvFor } from "../formal_layer.js";
import { assumptionCiteContext } from "../assumption_citations.js";
import { FIRST_DRAFT_BRIEF } from "../revision_brief.js";
import { symbolProseTargets, normalizeSymbolLeanrefs, promoteSymbolLeanrefs, repairSymbolLeanrefTargets } from "../emit.js";
import { lintIsolatedLemmas } from "../paper_graph.js";
import { writeJsonAtomic, writeTextAtomic } from "../json_io.js";
import { loadJsonCache } from "../cache.js";
import { recordP2Assembly } from "../assembly_freshness.js";
import { mapLimit } from "../gates.js";
import { proofFilePath } from "../proof_files.js";
import { applyProseRevision, applyTargetedReplacements, type TextReplacement } from "../prose_revision.js";
import { normalizeRawModelJson, repairLatexStringsDeep } from "../../discovery/core/latex_serialization.js";
import { runProofAudit, type ProofRenderHook } from "../audit.js";
import { extractFullDeclSource } from "../lean_extract.js";
import { discoverRealizedSymbols, buildSymbolClusters } from "../../formalization/crosswalk.js";
import { unconsumedStatementNodes, type FormalizationGraph } from "../graph_view.js";
import { parseBib } from "../citations.js";
import { resolveLeanDeclaration, resolvedLeanAbsolutePath } from "../declaration_resolver.js";
import { loadBankNarrative, loadInformalDerivations } from "../bank.js";
import { compactSectionOutline, priorSectionContext, type PriorSectionContext } from "../p2_section_context.js";

/** Content key for a P2 section cache entry: changes iff an input that SHAPES the prose changes —
 *  the section's objs list (membership AND order), brief, allowed cites, or its revision brief.
 *  Environment BODIES are deliberately NOT in the key: the drafter never authors them (the frozen
 *  layer is substituted mechanically by `normalizeFrozenEnvs` on every assembly, cache hit or not),
 *  so a re-rendered env swaps into the cached prose with no authoring call. Keying on bodies made
 *  one prompt edit re-draft nine sections and silently revert referee-repaired prose (2026-08-21).
 *  Prose that describes an env's content can go stale; the P3 gates and P5 referee review the
 *  assembled paper and catch that. An outline restructure that moves an env between sections
 *  changes the affected objs lists, so those sections re-draft rather than reuse a stale placement. */
export function sectionCacheKey(
  name: string, objs: string[], brief: string, allowedKeys: string, revBrief: string,
): string {
  return hashEnvBody([name, objs.join(","), brief, allowedKeys, revBrief].join("§"));
}

export interface ProofHelperContext { obj_id: string; tex: string }

/** Seed proof context with recorded dependencies and explicit paper references. The compact
 * catalogue keeps unrecorded dependencies discoverable without sending every statement body. */
export function proofHelperContextFor(
  envs: AnchoredEnv[], envText: ReadonlyMap<string, string>, graph: FormalizationGraph, targetObjId: string,
  additionalText = "",
): ProofHelperContext[] {
  const byId = new Map(envs.map(e => [e.obj_id, e]));
  const wanted = new Set(graph.edges.filter(e => e.from === targetObjId).map(e => e.to));
  const addRefs = (text: string) => {
    for (const match of stripTexComments(text).matchAll(/\\(?:Cref|cref|ref)\{([^}]+)\}/g)) {
      for (const label of match[1].split(",").map(s => s.trim())) {
        if (label.startsWith("obj:")) wanted.add(label.slice(4));
      }
    }
  };
  addRefs(`${byId.get(targetObjId)?.body ?? ""}\n${additionalText}`);
  // References inside an included statement must remain resolvable; cycles terminate by ID.
  for (const id of wanted) {
    const env = byId.get(id);
    if (env) addRefs(env.body);
  }
  return envs.filter(e => e.obj_id !== targetObjId && wanted.has(e.obj_id)).map(e => {
    const decl = leanPointer(graph, e.obj_id)?.decl;
    return { obj_id: e.obj_id,
      tex: `${decl ? `% realizes Lean declaration: ${decl}\n` : ""}${envText.get(e.obj_id)!}` };
  });
}

/** Complete object identities, without statement bodies. The writer can fetch any missing
 * premise by obj_id from formal_layer.json, including dependencies absent from the graph. */
export function proofObjectCatalog(envs: readonly AnchoredEnv[], graph: FormalizationGraph, targetObjId: string): string {
  return envs.filter(e => e.obj_id !== targetObjId).map(e =>
    `${e.obj_id} | ${(e.title ?? e.env).replace(/\s+/g, " ")} | ${leanPointer(graph, e.obj_id)?.decl ?? "no Lean declaration"}`,
  ).sort().join("\n");
}

/** Existing authored work is always a candidate for the mandatory current audit.
 * Render keys describe provenance, never permission to reuse an old approval. */
export async function existingProofForP2(
  proofPath: string, storedKey: string | undefined, currentKey: string,
): Promise<{ text: string; cacheHit: boolean } | null> {
  const text = await readFile(proofPath, "utf8").catch(() => null);
  return text === null ? null : { text, cacheHit: storedKey === currentKey };
}

function sortedProofHelperContext(context: ProofHelperContext[]): ProofHelperContext[] {
  const seen = new Set<string>();
  for (const entry of context) {
    if (seen.has(entry.obj_id)) throw new Error(`P2 proof helper context has duplicate obj_id ${entry.obj_id}`);
    seen.add(entry.obj_id);
  }
  return [...context].sort((a, b) => a.obj_id < b.obj_id ? -1 : a.obj_id > b.obj_id ? 1 :
    hashEnvBody(a.tex).localeCompare(hashEnvBody(b.tex)));
}

/** Proof helpers are a mathematical context set, not a presentation sequence.
 * Canonicalize only the cache-key view; the prompt retains formal-layer order. */
export function canonicalProofHelperContext(context: ProofHelperContext[]): string {
  return sortedProofHelperContext(context)
    .map(({ obj_id, tex }) => `${obj_id}\n${tex}`).join("\n\n");
}
const canonicalProofHelperTex = (context: ProofHelperContext[]): string =>
  sortedProofHelperContext(context)
    .map(({ tex }) => tex).join("\n\n");

export function proofRenderCacheKey(parts: {
  modelKey: string; objId: string; envTex: string; leanPath: string; leanDecl: string;
  exactDecl: string; helperContext: ProofHelperContext[]; notation: string; revisionBrief: string;
  citedDependencies: string; informalDerivation: string; objectCatalog?: string;
}): string {
  return hashEnvBody([
    parts.modelKey, "proof-helper-set-v2", parts.objId, parts.envTex, parts.leanPath, parts.leanDecl,
    parts.exactDecl, canonicalProofHelperContext(parts.helperContext), parts.notation,
    parts.revisionBrief, parts.citedDependencies, "citation-erasure-v1", parts.informalDerivation,
    ...(parts.objectCatalog === undefined ? [] : ["scoped-proof-context-v1", parts.objectCatalog]),
  ].join("§"));
}

/** The front-matter author must receive at least one verified citation key. */
export function frontMatterBibKeys(bibText: string): string {
  const keys = parseBib(bibText).map((entry) => entry.key);
  if (keys.length === 0) {
    throw new Error("P2 front-matter draft requires a non-empty, parseable references.bib citation pool");
  }
  return keys.join(", ");
}

/** Content key for the front-matter draft, including every model prompt input. */
export function frontMatterCacheKey(
  modelCacheKey: string, body: string, frontBrief: string, brief: string, allowedBibKeys: string,
): string {
  return hashEnvBody([modelCacheKey, body, frontBrief, brief, allowedBibKeys].join("§"));
}

/** Run-local Lean pointer for a paper object, from the graph (node id → decl).
 *  `null` for an object with no run-local decl (statement-only, or an external
 *  reuse decl with `file: null`). The graph carries no line number, so `line: 0`
 *  — the proof renderer locates the decl by name. */
function leanPointer(graph: FormalizationGraph, objId: string): { file: string; decl: string; line: number } | null {
  const n = graph.nodes.find((x) => x.id === objId);
  if (!n || !n.lean.decl_name || !n.lean.file) return null;
  return { file: n.lean.file, decl: n.lean.decl_name, line: 0 };
}


/** Strip heading decoration that would DOUBLE the letter `\appendix` prints. LaTeX numbers
 *  appendix sections A, B, … by itself, so a drafter-supplied "Appendix:", "Appendix B:", or
 *  a bare enumerator "B: " / "B. " / "B) " renders as "B B: …". Applied repeatedly because the
 *  spellings compose ("Appendix B: proofs"); a single letter is only stripped when followed by
 *  enumerator punctuation, so a title like "A note on codes" survives. */
export function stripAppendixHeadingDecoration(sectionHead: string): string {
  const m = /^(\\section\{\s*)([\s\S]*)$/.exec(sectionHead);
  if (!m) return sectionHead;
  let title = m[2];
  for (let i = 0; i < 3; i++) {
    const next = title
      .replace(/^Appendix\s*[A-Z]?\s*[:.)]?\s+/i, "")
      .replace(/^[A-Z][:.)]\s+/, "");
    if (next === title) break;
    title = next;
  }
  // Sentence case: the stripped enumerator carried the capital ("A: proofs…"), so a title
  // left starting with a lowercase ASCII letter must be re-capitalized — otherwise the
  // appendix reads "A proofs for identification…" next to "E Proofs of the main results".
  // Only a plain leading letter is touched: a title opening with math or a macro is left as is.
  if (title !== m[2] && /^[a-z]/.test(title)) title = title[0].toUpperCase() + title.slice(1);
  return m[1] + title;
}

/**
 * P2 — section-by-section body draft (codex, high effort), Lean-faithful appendix proofs
 * (codex + lean-lsp), abstract/intro written last from the finished body.
 * The assembled paper.tex must pass the anchor + frozen-body lint before the
 * draft checkpoint; a P2 that breaks the frozen layer never reaches the user.
 */
export async function stageP2(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p2.stub"), "dry-run\n");
    return;
  }
  // BALLAST GATE: an unconsumed frozen theorem/lemma enters the paper only with
  // an explicit operator acknowledgment. A headline result is acknowledged once
  // in ballast_review.json; motivation-only standard material is excised instead
  // (nl.frozen=false in the bank graph). Fails CLOSED so ballast cannot slip
  // into the presentation stages silently (two-category incident, 2026-08-27).
  {
    const ackPath = join(io.outDir, "ballast_review.json");
    const acks = await readFile(ackPath, "utf8")
      .then((raw) => (JSON.parse(raw) as { acknowledged?: Record<string, string> }).acknowledged ?? {})
      .catch(() => ({}) as Record<string, string>);
    const unconsumed = unconsumedStatementNodes(io.bank.graph, new Set(Object.keys(acks)));
    {
      const unacked = unconsumed.filter((n) => !acks[n.id]);
      if (unacked.length > 0) {
        throw new Error(
          `P2 ballast gate: ${unacked.length} frozen statement(s) nothing consumes would enter the paper: ` +
            `[${unacked.map((n) => n.id).join(", ")}]. For each: a delivered headline/benchmark is acknowledged ` +
            `once in ${ackPath} under {"acknowledged": {"<id>": "<why it belongs>"}}; motivation-only standard ` +
            `material is excised instead (set nl.frozen=false on the bank node and remove it from the outline).`,
        );
      }
    }
  }
  const outlineRaw = await readFile(join(io.outDir, "outline.md"), "utf8");
  // Source of truth: the JSON formal layer. Envs are assembled MECHANICALLY from the blocks (via
  // texEnvFor — the same helper P1 uses to derive the .tex view), so the frozen statement that
  // reaches paper.tex is byte-identical to the source and the P4 equality lint is exact.
  const layerSrc = FormalLayerSource.parse(
    JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")),
  );
  const legacyFormalRefs = layerSrc.blocks.filter((b) => /\\(?:auto|eq)?ref\{/.test(b.body));
  if (legacyFormalRefs.length > 0) {
    throw new Error(
      `P2 requires a P1 cleveref refresh: ${legacyFormalRefs.length} frozen formal object(s) still use legacy \\ref ` +
      `(${legacyFormalRefs.map((b) => b.obj_id).join(", ")}). Re-run from P1 so formal_layer.json remains the source of truth.`,
    );
  }
  const frozen: Record<string, string> = Object.fromEntries(layerSrc.blocks.map((b) => [b.obj_id, b.body]));
  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8");
  const outline = parseOutline(outlineRaw);
  // D-stage informal derivations: exposition context for the proof renderer. UNTRUSTED —
  // the prompt subordinates them to the Lean route and the P2 proof audit rejects any
  // non-Lean route, so a wrong or never-formalized derivation cannot be laundered in.
  const informalDerivations = await loadInformalDerivations(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec);
  const narrative = await loadBankNarrative(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec);
  const informalDerivationFor = (objId: string): string =>
    informalDerivations.get(objId) ?? "(none recorded for this result)";

  const envBlocks = layerSrc.blocks.filter((b) => b.env);
  const envs: AnchoredEnv[] = envBlocks.map((b, i) => ({
    env: b.env!,
    obj_id: b.obj_id,
    title: b.title,
    body: b.body,
    order: i,
  }));
  const envText = new Map(envBlocks.map((b) => [b.obj_id, texEnvFor(b)]));
  const blockById = new Map(envBlocks.map((b) => [b.obj_id, b] as const));
  const citedDependencyPromptFor = (objId: string): string => {
    const deps = blockById.get(objId)?.cited_dependencies ?? [];
    if (deps.length === 0) return "(none)";
    return deps.map((d) => {
      const cite = d.cite_key ? `\\citep{${d.cite_key}}` : d.cite_id;
      return `- ${cite}${d.locator ? `, ${d.locator}` : ""}: ${d.statement.replace(/\s+/g, " ").trim()} ` +
        `(published source proof not formalized here; invoke it as cited literature, not as an assumption of this paper)`;
    }).join("\n");
  };
  validatePlacement(outline, envs);
  // A proved result is presented under a proof-bearing environment: proofs are rendered by env
  // kind, so a theorem/lemma re-kinded to a remark or algorithm would silently ship unproved.
  {
    const proofBearing = new Set(["theoremv", "propositionv", "lemmav"]);
    const demoted = envBlocks.filter((b) => {
      const n = io.bank.graph.nodes.find((x) => x.id === b.obj_id);
      return n && (n.kind === "theorem" || n.kind === "lemma") && n.lean.decl_name && n.delivery?.status !== "undelivered" && !proofBearing.has(b.env!);
    });
    if (demoted.length > 0) {
      throw new Error(
        `P2: proved result(s) presented without a proof-bearing environment — ${demoted.map((b) => `${b.obj_id} as ${b.env}`).join(", ")}; ` +
          `use theoremv/propositionv/lemmav (env_overrides in outline.md), then re-run from P1`,
      );
    }
  }

  // From-note objects (setup/definition/assumption) the prose may inline-link to their Lean via
  // \leanref. Listed by obj-id so the author uses the exact key the drawer/P4 validation resolves.
  const leanrefObjects = io.bank.graph.nodes
    .filter(
      (n) =>
        n.provenance === "from-note" &&
        (n.kind === "setup" || n.kind === "definition" || n.kind === "assumption"),
    )
    .map(
      (n) =>
        `${n.obj_id ?? n.id} [${n.kind}]: ${(n.nl?.statement ?? "").replace(/\s+/g, " ").slice(0, 140)}`,
    )
    .join("\n");

  // Core symbols realized in Lean (the `@realizes` tags): the draft links each one's NOTATION inline
  // via \leanref{sym:<name>}{<math>} at its first mention, so a reader can click the symbol itself
  // (μ_a, e_P, …) to see how it is realized. Derived from the Lean tags, generic preferred over arms.
  const leanDir = join(io.ctx.repoRoot, io.bank.leanSubdir);
  const symTargets = symbolProseTargets(
    await buildSymbolClusters(leanDir, (await discoverRealizedSymbols(leanDir)).map((name) => ({ name }))),
  );
  // Editable prose has one representation in authored sources and the assembled paper.
  // P3's exact patches must match both; frozen environments are restored afterward.
  const normalizeSymbols = (tex: string) => promoteSymbolLeanrefs(normalizeSymbolLeanrefs(
    repairSymbolLeanrefTargets(tex, symTargets.map((t) => t.name)),
  ));
  const symbolLeanrefTargets =
    symTargets
      .map((t) => `sym:${t.name} [symbol]: ${t.description.replace(/\s+/g, " ").slice(0, 140)}`)
      .join("\n") || "(none)";

  // Assumption citation provenance: the paper's references.bib (P0-curated) is the bib
  // namespace; each standard assumption's discovery cite is reconciled to a paper key (or a
  // fresh entry is injected). Computed per section so the drafter glosses + cites the
  // assumptions IT presents; injections are appended to references.bib once, after drafting.
  const bibPath = join(io.outDir, "references.bib");
  const bibText = await readFile(bibPath, "utf8").catch(() => "");
  const bibInjections = new Map<string, string>(); // dedup by injected key

  // body sections (abstract/introduction are written last)
  const bodySections = outline.sections.filter((s) => !/^(abstract|introduction)$/i.test(s.name));
  const isAppendixSection = (name: string) => /^appendix\b/i.test(name.trim());
  const sectionTexs: string[] = [];
  const priorDraftedSections: PriorSectionContext[] = [];
  const appendixTexs: string[] = [];
  await mkdir(join(io.outDir, "sections"), { recursive: true });
  // Content-keyed section cache: a section is reused only when its DRAFTING INPUTS are unchanged
  // (its objs set, brief, allowed cites, the frozen env bodies it places, and the revision brief).
  // An outline restructure that moves an env between sections changes the affected sections' objs,
  // so they re-draft instead of shipping a stale env placement (which the P4 ref-lint would reject).
  const cacheKeyPath = join(io.outDir, "sections", "_cache_keys.json");
  const cacheKeys = await loadJsonCache<Record<string, string>>(cacheKeyPath);
  const modelCacheKey = `${io.ctx.deps.codexModel ?? "unspecified-codex-model"}|${PRESENTATION_PROSE_POLICY_VERSION}`;
  for (let i = 0; i < bodySections.length; i++) {
    const s = bodySections[i];
    const name = `${String(i + 1).padStart(2, "0")}_${s.name.toLowerCase().replace(/[^a-z0-9]+/g, "_")}.tex`;
    // Citation guidance + resolved keys for THIS section's assumptions (computed even when the
    // section is cache-hit, so references.bib still receives the injected entries on a P2 retry).
    const aCtx = assumptionCiteContext(io.bank.graph, s.objs, bibText);
    for (const e of aCtx.injections) {
      const k = e.match(/@\w+\s*\{\s*([^,\s]+)/)?.[1];
      if (k) bibInjections.set(k, e);
    }
    const citedKeys = s.objs.flatMap((id) =>
      (blockById.get(id)?.cited_dependencies ?? []).flatMap((d) => d.cite_key ? [d.cite_key] : []),
    );
    const allowedKeys = [...new Set([...s.bib, ...aCtx.extraKeys, ...citedKeys])].join(", ");
    const citedNotes = s.objs
      .filter((id) => (blockById.get(id)?.cited_dependencies.length ?? 0) > 0)
      .map((id) => `${id}:\n${citedDependencyPromptFor(id)}`)
      .join("\n\n") || "(none)";
    const revBrief = FIRST_DRAFT_BRIEF;
    // D-stage per-result notes for THIS section's objects: why each result matters and what
    // it unlocks, plus the D-stage condition text behind each assumption. Grounded motivation
    // for the prose the prompt demands — subordinated to the frozen envs.
    const resultNotes = s.objs
      .map((id) => {
        const note = narrative.statementNotes.get(id);
        const condition = narrative.assumptionConditions.get(id);
        const parts = [
          note?.justification && `why it matters: ${note.justification}`,
          note?.consumer && `what it unlocks: ${note.consumer}`,
          condition && `D-stage condition: ${condition}`,
        ].filter(Boolean);
        return parts.length > 0 ? `${id}:\n${parts.join("\n")}` : "";
      })
      .filter(Boolean)
      .join("\n\n") || "(none recorded)";
    // Content key: re-draft when a prose-shaping input changes (objs/brief/cites/revision/notes);
    // env bodies are substituted mechanically below and are NOT a drafting input.
    const sectionKey = hashEnvBody([modelCacheKey, sectionCacheKey(name, s.objs, s.brief, allowedKeys, `${revBrief}\n${citedNotes}\n${resultNotes}`)].join("§"));
    // Artifact cache, content-keyed: an unchanged section is reused (a P2 retry does not re-draft);
    // a changed objs/brief/env-set re-drafts. Delete sections/ to force a full regenerate.
    let tex = io.reassemble || cacheKeys[name] === sectionKey ? await readFile(join(io.outDir, "sections", name), "utf8").catch(() => null) : null;
    if (tex === null) {
      // Codex drafts the body section; high effort (the main faithful prose, must
      // match the frozen envs + outline and cite only the allowed keys).
      const { stdout: reply } = await io.ctx.deps.runCodex({
        prompt: await presentationPrompt("p2_section", {
          outline: compactSectionOutline(outline),
          section_brief: `## section: ${s.name}\n${s.brief}`,
          frozen_envs_for_section: s.objs.map((id) => envText.get(id)!).join("\n\n"),
          allowed_bib_keys: allowedKeys,
          assumption_notes: aCtx.notes || "(no assumptions in this section)",
          result_notes: resultNotes,
          cited_dependency_notes: citedNotes,
          notation_table: outline.notation,
          prior_sections: priorSectionContext(priorDraftedSections),
          leanref_objects: leanrefObjects || "(none)",
          symbol_leanref_targets: symbolLeanrefTargets,
          revision_brief: revBrief,
        }),
        cwd: io.ctx.repoRoot,
        reasoningEffort: "high",
        leanLsp: false,
      });
      tex = unwrapArtifact(reply, ["latex", "tex"], "tex");
    }
    tex = stripRedundantEnvLabels(tex);
    // Normalize authored prose before restoring frozen text: reference cleanup may
    // otherwise strip intentional math wrappers from a canonical environment.
    tex = normalizeSymbols(normalizeCrefs(tex));
    // The frozen layer is the trust anchor: mechanically substitute every
    // anchored env with its canonical text (models sometimes paraphrase while
    // "copying exactly"; that must never reach the lint as drift).
    tex = normalizeFrozenEnvs(tex, envText);
    // The outline's objs order IS the paper order P1 certified (definitions before first use). The
    // frozen text is identical wherever it is printed, so a drafter's placement slips — a
    // duplicate, an omitted block, an env another section owns, a permutation — each have one
    // determined repair; the prose around a mechanically placed block is P3/P5's to review.
    const sectionOrder = s.objs.filter(id => blockById.get(id)?.env != null);
    const placed = placeFrozenEnvs(tex, sectionOrder, envText);
    for (const repair of placed.repairs) io.state.notes.push(`P2: section ${s.name} — ${repair}`);
    tex = placed.tex;
    const placementProblems = lintEnvOrder(tex, sectionOrder);
    if (placementProblems.length > 0) {
      throw new Error(`P2 section ${s.name}: ${placementProblems.map(p => p.detail).join("; ")}`); // unreachable after placement — a bug, not a draft defect
    }
    tex = normalizeCitedScopeFootnotes(tex, envBlocks);
    await writeTextAtomic(join(io.outDir, "sections", name), tex.replace(/\n+$/, "") + "\n"); // a truncated section behind a valid key would be reused silently
    priorDraftedSections.push({ name: s.name, objs: s.objs, path: join(io.outDir, "sections", name), tex });
    cacheKeys[name] = sectionKey;
    // Persist the key with its section: a crash in a LATER section or in the proof
    // loop must not discard this draft's cache entry (a retry would re-pay every
    // high-effort section call — the stated P2-retry-reuse contract).
    await writeJsonAtomic(cacheKeyPath, cacheKeys);
    if (isAppendixSection(s.name)) {
      // Placed after \appendix below, which auto-letters each section (A, B, …). Strip any heading
      // decoration the drafter added that would DOUBLE that letter: an "Appendix:" prefix (→ "A
      // Appendix: …") or a redundant manual "A. "/"B. " letter prefix (→ "A A. …").
      tex = tex.replace(/\\section\{[^}]*/, (h) => stripAppendixHeadingDecoration(h));
      appendixTexs.push(tex);
    } else {
      sectionTexs.push(tex);
    }
  }

  // Append the reconciliation injections (standard assumptions whose discovery reference is
  // NOT already in the paper's references.bib under any key) so every \citep resolves. Idempotent:
  // skip any key already present (a re-run, or a paper key reused by reconciliation).
  if (bibInjections.size > 0) {
    const current = await readFile(bibPath, "utf8").catch(() => "");
    // Escape the key: a `.`/`+` in a bib key would otherwise widen the match and
    // read an absent entry as "already present", leaving a dangling \citep.
    const fresh = [...bibInjections]
      .filter(([k]) => !new RegExp(`@\\w+\\s*\\{\\s*${k.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![\\w-])`).test(current))
      .map(([, e]) => e);
    if (fresh.length > 0) {
      await writeFile(
        bibPath,
        current.trimEnd() + "\n\n% --- assumption citation provenance (causalsmith P2) ---\n" + fresh.join("\n\n") + "\n",
        "utf8",
      );
    }
  }

  // Read after the provenance injection above: the front-matter author receives the complete
  // paper-wide verified bibliography pool, while section authors receive strict per-section subsets.
  const frontMatterBib = await readFile(bibPath, "utf8").catch(() => {
    throw new Error("P2 front-matter draft requires a readable references.bib citation pool");
  });
  const allowedFrontMatterBibKeys = frontMatterBibKeys(frontMatterBib);

  // Lean-faithful appendix proofs, one per theorem env. Cached per theorem in
  // proofs/<obj_id>.tex — see proof_files.ts for the portable spelling of the id
  // (codex renders are the most expensive P2 calls); delete a file to re-render that proof.
  // Include recorded dependencies and explicit references; missing graph edges remain
  // discoverable through a complete compact catalogue and targeted formal-layer reads.
  const helperContextFor = (objId: string, additionalText = "") =>
    proofHelperContextFor(envs, envText, io.bank.graph, objId, `${informalDerivationFor(objId)}\n${additionalText}`);
  const objectCatalogFor = (objId: string) => proofObjectCatalog(envs, io.bank.graph, objId);
  const theoremProofById = new Map<string, string>();
  const lemmaProofTexts = new Map<string, string>();
  await mkdir(join(io.outDir, "proofs"), { recursive: true });
  const proofCacheKeyPath = join(io.outDir, "proofs", "_cache_keys.json");
  const proofCacheKeys = await loadJsonCache<Record<string, string>>(proofCacheKeyPath);
  const repairContextKeys = new Map<string, string>();
  const proofRenderKey = async (
    objId: string,
    envTex: string,
    lean: { file: string; decl: string },
    helperContext: ProofHelperContext[],
    revisionBrief: string,
  ) => {
    const resolved = await resolveLeanDeclaration(io.ctx.repoRoot, io.bank.leanSubdir,
      { file: lean.file, decl: lean.decl, line: 0 });
    const leanPath = await resolvedLeanAbsolutePath(io.ctx.repoRoot, resolved.file);
    const exactDecl = extractFullDeclSource(await readFile(leanPath, "utf8"), resolved.decl, resolved.line);
    const canonicalHelpers = canonicalProofHelperTex(helperContext);
    const notation = notationForArtifact(outline.notation, `${envTex}\n${exactDecl}\n${canonicalHelpers}`);
    // Keyed on the workspace-relative source so a checkout path is not a render input.
    return proofRenderCacheKey({ modelKey: modelCacheKey, objId, envTex, leanPath: resolved.file, leanDecl: resolved.decl,
      exactDecl, helperContext, notation, revisionBrief, citedDependencies: citedDependencyPromptFor(objId),
      informalDerivation: informalDerivationFor(objId), objectCatalog: objectCatalogFor(objId) });
  };
  /** ONE writer for a result's proof: the first render and every judge-driven repair go through
   *  this prompt. A repair passes the prior proof and the judge's tagged issues as defects. */
  const renderProofOnce = async (
    objId: string,
    lean: { file: string; decl: string },
    repair?: { priorProof: string; defects: string[]; previousIssues: readonly string[] },
  ): Promise<string> => {
    const helperTex = helperContextFor(objId, repair ? `${repair.priorProof}\n${[...repair.defects, ...repair.previousIssues].join("\n")}` : "")
      .map(({ tex }) => tex).join("\n\n");
    const resolved = await resolveLeanDeclaration(io.ctx.repoRoot, io.bank.leanSubdir, { ...lean, line: 0 });
    const leanPath = await resolvedLeanAbsolutePath(io.ctx.repoRoot, resolved.file);
    const exactDecl = extractFullDeclSource(await readFile(leanPath, "utf8"), resolved.decl, resolved.line);
    const { stdout } = await io.ctx.deps.runCodex({
      prompt: await presentationPrompt("p2_proof", {
        theorem_env: envText.get(objId)!,
        lean_proof_source: `file: ${leanPath}\ndeclaration: ${resolved.decl}\n\n${exactDecl || "Read this declaration from the file; no exact excerpt was resolved."}`,
        helper_lemma_envs: helperTex || "(no recorded paper dependency; consult the catalogue if the Lean route uses another paper object)",
        paper_object_catalog: objectCatalogFor(objId),
        formal_layer_path: join(io.outDir, "formal_layer.json"),
        outline_path: join(io.outDir, "outline.md"),
        cited_dependencies: citedDependencyPromptFor(objId),
        informal_derivation: informalDerivationFor(objId),
        notation_table: notationForArtifact(outline.notation, `${envText.get(objId)!}\n${helperTex}`),
        revision_brief: FIRST_DRAFT_BRIEF,
        prior_and_defects: repair
          ? `prior_proof:\n${repair.priorProof}\n\nCurrent defects to repair:\n${repair.defects.map((d) => `- ${d}`).join("\n")}\n\nEarlier findings (retain their corrections; check against current source if still relevant):\n${repair.previousIssues.map(d => `- ${d}`).join("\n") || "(none)"}`
          : "(first render — none)",
      }),
      cwd: io.ctx.repoRoot,
      reasoningEffort: "high",
      leanLsp: true,
    });
    return stdout;
  };
  /** The proof judge's repair channel: re-render with the issues as defects; `null` when the
   *  renderer reports UNCLEAR or emits an invalid patch (the prior proof then stands and halts). */
  const repairProof: ProofRenderHook = async (objId, priorProof, issues, previousIssues) => {
    const lean = leanPointer(io.bank.graph, objId);
    if (!lean) return null;
    const stdout = await renderProofOnce(objId, lean, { priorProof, defects: issues, previousIssues });
    const patched = parseProofRepair(stdout, priorProof);
    if (patched === null) io.state.notes.push(`P2: ${objId} repair returned invalid exact replacements; kept the prior proof (see agent_calls.log)`);
    return patched;
  };
  // One writer for main results and lemmas; audit repairs patch its existing proof. Bounded
  // concurrency replaces sequential singleton "batches"; each paid result persists immediately.
  // A result whose route the writer cannot render is recorded, not thrown: its siblings still
  // render and are judged in this pass, and the halt below lists every such result at once.
  const renderFailures: string[] = [];
  try {
    await mapLimit(envs.filter((e) => isMainProofEnv(e.env) || e.env === "lemmav"), 4, async (e) => {
      const lean = leanPointer(io.bank.graph, e.obj_id);
      if (!lean) return;
      const proofPath = proofFilePath(io.outDir, e.obj_id);
      const proofKey = await proofRenderKey(e.obj_id, envText.get(e.obj_id)!, lean, helperContextFor(e.obj_id), FIRST_DRAFT_BRIEF);
      repairContextKeys.set(e.obj_id, proofKey);
      const output = isMainProofEnv(e.env) ? theoremProofById : lemmaProofTexts;
      const existing = await existingProofForP2(proofPath, proofCacheKeys[e.obj_id], proofKey);
      if (existing !== null) {
        output.set(e.obj_id, canonicalizeProofTitle(e.obj_id, normalizeCrefs(existing.text.trim())));
        if (!existing.cacheHit) io.state.notes.push(`P2: reused existing proof candidate ${e.obj_id} for mandatory current audit (render cache remains missed)`);
        return;
      }
      let proof: string | null = null;
      for (let attempt = 0; attempt < 2 && proof === null; attempt++) {
        const stdout = await renderProofOnce(e.obj_id, lean);
        const unclear = stdout.match(/^\s*UNCLEAR:\s*(.*)$/m);
        if (unclear) {
          renderFailures.push(`${e.obj_id}: the writer reported the Lean route UNCLEAR — ${unclear[1].trim().slice(0, 300)}`);
          return;
        }
        proof = parseProofRender(stdout, e.obj_id);
      }
      if (proof === null) {
        renderFailures.push(`${e.obj_id}: no proof block after a targeted retry (see agent_calls.log)`);
        return;
      }
      await writeTextAtomic(proofPath, proof + "\n");
      proofCacheKeys[e.obj_id] = proofKey;
      await writeJsonAtomic(proofCacheKeyPath, proofCacheKeys);
      output.set(e.obj_id, proof);
    });
  } finally {
    await writeJsonAtomic(proofCacheKeyPath, proofCacheKeys);
  }

  // ── PROOF EQUIVALENCE AUDIT (co-located with proof production). The moment every appendix proof is
  // rendered, judge each one's prose against its machine-verified Lean proof; an unfaithful proof is
  // re-rendered by `repairProof` with the judge's issues as defects and proofs/<id>.tex rewritten. A
  // residual unfaithful proof halts P2 rather than reaching the draft checkpoint.
  const proofTargets = envs
    .filter((e) => isMainProofEnv(e.env) || e.env === "lemmav")
    .map((e) => ({ e, lean: leanPointer(io.bank.graph, e.obj_id) }))
    .filter((x): x is { e: AnchoredEnv; lean: { file: string; decl: string; line: number } } => x.lean !== null)
    .map(({ e, lean }) => ({ obj_id: e.obj_id, isMain: isMainProofEnv(e.env), lean: { file: lean.file, decl: lean.decl } }));
  const { refined: refinedProofs, problems: proofProblems } = await runProofAudit(io, proofTargets, repairProof, repairContextKeys);
  // A judge-faithful proof is the render output for its current inputs: record its key so a later
  // entry reuses it as a hit, not as a "candidate with a missed render cache" note.
  const unfaithful = new Set(proofProblems.map((p) => p.objId));
  for (const [id, proofKey] of repairContextKeys) {
    if (refinedProofs.has(id) && !unfaithful.has(id)) proofCacheKeys[id] = proofKey;
  }
  await writeJsonAtomic(proofCacheKeyPath, proofCacheKeys);
  if (renderFailures.length > 0) {
    throw new Error(
      `${PROOF_AUDIT_RENDERING_MARKER} (${renderFailures.length} proof(s) could not be rendered — fix the Lean route ` +
        `or mapping, or adjudicate; re-entry renders only these): ${renderFailures.join("; ")}` +
        (proofProblems.length > 0 ? `. Also unfaithful after repair: ${proofProblems.map((p) => p.detail).join("; ")}` : ""),
    );
  }
  if (proofProblems.length > 0) {
    // Promotion (a new citable lemma) can only close a `[missing-step]` gap. Everything else is a
    // rendering defect the renderer could not repair in its rounds — halt for adjudication under a
    // marker the pipeline never promotes on, so a rendering defect cannot cascade into lemmas.
    const promotable = proofProblems.filter((p) => p.promotable);
    const marker = promotable.length > 0 ? PROOF_AUDIT_FAILURE_MARKER : PROOF_AUDIT_RENDERING_MARKER;
    throw new Error(
      `${marker} (${proofProblems.length} proof(s) still unfaithful after repair — ` +
        (promotable.length > 0
          ? `${promotable.length} with a missing derivation a promoted lemma can supply): `
          : `adjudicate, or delete the proof file for <id> under proofs/ (its colon is spelled --) to re-render from scratch): `) +
        proofProblems.map((p) => p.detail).join("; "),
    );
  }
  // Assembly uses the REFINED proofs (override the freshly-rendered maps).
  for (const [id, proof] of refinedProofs) {
    // A repair render may rewrite the title line (observed: dropping the obj: prefix,
    // which makes the proof invisible to lintProofsReachedPaper AND leaks a bare
    // obj_id into prose) — canonicalize on this path too, not only on render/reuse.
    const canonicalProof = canonicalizeProofTitle(id, normalizeCrefs(proof));
    if (theoremProofById.has(id)) theoremProofById.set(id, canonicalProof);
    if (lemmaProofTexts.has(id)) lemmaProofTexts.set(id, canonicalProof);
  }
  await writeFile(
    join(io.outDir, "appendix_proofs.tex"),
    envs
      .filter((e) => isMainProofEnv(e.env))
      .map((e) => theoremProofById.get(e.obj_id))
      .filter((p): p is string => !!p)
      .join("\n\n") + "\n",
    "utf8",
  );

  // Lemma proof placement follows the outline's statement placement. A lemma whose statement env
  // sits in an APPENDIX section keeps its proof inline (statement → proof). A lemma the outline
  // placed in a BODY section is shown statement-only there, with its proof DEFERRED to the
  // consolidated proofs appendix (mirrors how a body theorem defers its proof) and a forward
  // pointer added after the statement — otherwise the body lemma would print with no proof anywhere.
  const PROOFS_LABEL = "sec:deferred-proofs";
  const bodyObjIds = new Set(outline.sections.filter((s) => !isAppendixSection(s.name)).flatMap((s) => s.objs));
  const bodyLemmaIds = new Set(
    envs
      .filter((e) => e.env === "lemmav" && bodyObjIds.has(e.obj_id) && lemmaProofTexts.has(e.obj_id))
      .map((e) => e.obj_id),
  );

  // Appendix lemmas: proof inline after the statement. Body lemmas: NOT inlined here.
  const appendixWithProofs = appendixTexs.map((tex) => insertLemmaProofs(tex, lemmaProofTexts));
  // Body lemmas: a "proof deferred" pointer after the statement.
  const bodyWithPointers =
    bodyLemmaIds.size > 0 ? sectionTexs.map((tex) => insertProofPointers(tex, bodyLemmaIds, PROOFS_LABEL)) : sectionTexs;
  // Consolidated proofs appendix: main-result theorems + body-placed lemmas, in paper (env) order.
  const proofById = new Map<string, string>([...lemmaProofTexts, ...theoremProofById]);
  const deferredProofs = envs
    .filter((e) => isMainProofEnv(e.env) || (e.env === "lemmav" && bodyLemmaIds.has(e.obj_id)))
    .map((e) => proofById.get(e.obj_id))
    .filter((p): p is string => !!p);

  const body = [
    ...bodyWithPointers,
    // Clear body→appendix separator. After \appendix the article class letters each section (A, B,
    // …) but prints no "Appendix" word, and tex2html strips \appendix entirely on the web — so without
    // this heading neither output marks where the main body ends. \section* is unnumbered (does not
    // consume the appendix letter counter) and passes through pandoc as an <h1> divider on the web.
    "\\appendix",
    "\\section*{Appendices}",
    ...appendixWithProofs,
    ...(deferredProofs.length > 0
      ? [`\\section{Proofs of the main results}\\label{${PROOFS_LABEL}}`, deferredProofs.join("\n\n")]
      : []),
    "\\bibliographystyle{plainnat}",
    "\\bibliography{references}",
  ].join("\n\n");

  // Front matter summarizes the finished exposition and statements. Separate proof derivations
  // are audited for correctness but do not need to be resent to the abstract/intro author.
  const frontBrief = FIRST_DRAFT_BRIEF;
  // D-stage contribution narrative for the front matter — motivation/positioning only,
  // subordinated to the body (the prompt forbids importing any claim the body lacks).
  const contributionNarrative = [
    narrative.tldr && `TLDR (pre-formalization research summary):\n${narrative.tldr}`,
    narrative.projectJustification && `Project justification:\n${narrative.projectJustification}`,
    narrative.interpretation && `Interpretation:\n${narrative.interpretation}`,
    narrative.honestScope && `Honest scope (claims the research stage itself disclaims — never contradict this):\n${narrative.honestScope}`,
  ].filter(Boolean).join("\n\n") || "(none recorded)";
  // Introduction needs delivered statements and exposition, not the separately audited proofs.
  const frontBody = [...sectionTexs, "\\appendix", "\\section*{Appendices}", ...appendixTexs,
    ...(deferredProofs.length > 0 ? ["\\section{Proofs of the main results}"] : []),
  ].join("\n\n");
  const frontKey = frontMatterCacheKey(modelCacheKey, frontBody, frontBrief, `${brief}\n${contributionNarrative}`, allowedFrontMatterBibKeys); // why: key the exact exposition/statement context and bibliography the author receives.
  const frontCacheHit = cacheKeys["_front"] === frontKey;
  // Reassemble mode: front_matter.tex is the reviser's authored text — reuse it
  // regardless of the body-keyed cache (the revised body WILL have changed the key;
  // re-drafting here would clobber the revision), and bless the new key below.
  let front = io.reassemble || frontCacheHit ? await readFile(join(io.outDir, "front_matter.tex"), "utf8").catch(() => null) : null;
  if (front !== null && io.reassemble) front = normalizeCrefs(front);
  if (front === null) {
    // Intro + abstract: medium effort (summarization of the already-drafted body).
    front = unwrapArtifact(
      (
        await io.ctx.deps.runCodex({
          prompt: await presentationPrompt("p2_intro_abstract", {
            full_body_tex: frontBody,
            related_work_brief: brief,
            contribution_narrative: contributionNarrative,
            allowed_bib_keys: allowedFrontMatterBibKeys,
            revision_brief: frontBrief,
          }),
          cwd: io.ctx.repoRoot,
          reasoningEffort: "medium",
          leanLsp: false,
        })
      ).stdout,
      ["latex", "tex"],
      "tex",
    );
    // The affirmative-prose contract is P3's hard gate, repaired there by exact patches; P2 does
    // not also halt on it (a halt here only re-drafts the whole text at the next entry).
    front = normalizeCrefs(front);
    await writeTextAtomic(join(io.outDir, "front_matter.tex"), front + "\n");
  }
  cacheKeys["_front"] = frontKey;
  await writeJsonAtomic(cacheKeyPath, cacheKeys);

  const macros = await readFile(join(import.meta.dirname, "..", "templates", "paper_macros.tex"), "utf8");
  await writeFile(join(io.outDir, "paper_macros.tex"), macros, "utf8");
  const paper = [
    "\\documentclass[11pt]{article}",
    "\\usepackage[margin=1.1in]{geometry}",
    "\\usepackage{amssymb,mathtools,natbib}",
    "\\input{paper_macros.tex}",
    `\\title{${outline.title}}`,
    // Scope the verification claim accurately but PAPER-AGNOSTICALLY: the footnote states
    // only what is true of every bundle and defers the exact scope to the verification
    // appendix. The previous fixed clause ("a result from the literature ... enters as a
    // published input rather than a Lean-checked step") was FALSE for papers with no
    // external formal dependencies — it contradicted the same document's verification
    // appendix, and referees read that as a trust-boundary defect no reviser could fix
    // (P5 major finding in three rounds, 2026-08-26).
    "\\author{CausalSmith\\thanks{Machine-generated by the CausalSmith research pipeline. Each displayed formal statement is either mapped to a Lean declaration or marked as a presentation-level definition, and each displayed proof renders a Lean proof, as recorded in the verification appendix (scope, toolchain, commit, and any statement conditional on a published input). Cited work otherwise supplies framing and positioning.}}",
    "\\date{\\today}",
    "\\begin{document}",
    "\\maketitle",
    front,
    body,
    "\\end{document}",
  ].join("\n\n");
  // Make every symbol `\leanref{sym:…}{…}` math-mode-safe (`\ensuremath`) so a display the drafter put
  // inside a `\(…\)` (a `$…$` nested in `\(…\)` is a fatal TeX error) still compiles at P4; then PROMOTE
  // any symbol link that leads a `\(…\)` to standalone, so the symbol stays clickable on the web instead
  // of being stripped to bare math (the drafter often writes the first mention as `\(\leanref…=…\)`).
  const paperNorm = normalizeSymbols(paper);
  // Repair cleveref object ids (proof bodies sometimes drop a kind prefix → silent "??") against
  // the labels the paper actually defines; a residual dangling ref fails the stage loud.
  const definedIds = new Set(parseAnchoredEnvs(paperNorm).map((e) => e.obj_id));
  const { tex: linkedPaper, problems: refProblems } = repairObjRefs(paperNorm, definedIds);
  // Finish at the same canonical boundary P3/P5 use, AFTER inserting proofs and
  // boilerplate. Otherwise their guard can mistake its own scope-note relocation
  // or frozen-text restoration for a protected edit in an unrelated prose patch.
  const paperSafe = applyProseRevision({
    before: linkedPaper, revised: linkedPaper, blocks: layerSrc.blocks, who: "P2 assembly",
  });

  // The formal layer is the paper's complete environment namespace. It includes graph-backed
  // objects plus P1's presentation-owned setup definitions; only the former require crosswalk/Lean
  // anchors, but both are valid frozen env ids for the P2 anchor lint.
  const known = new Set(layerSrc.blocks.map((b) => b.obj_id));
  const problems = [
    ...lintAnchors(paperSafe, known, new Map(Object.entries(frozen))),
    // The paper prints the frozen environments once each, in the P1 order (P3/P4 assert the same).
    ...lintEnvOrder(paperSafe, layerSrc.blocks.filter((b) => b.env !== null).map((b) => b.obj_id)),
    ...lintReferences(paperSafe),
    ...lintProofsReachedPaper(paperSafe, proofById.keys()),
    // Assembly is where a lemma's citations become visible for the first time (proofs are rendered
    // per-object, so no earlier stage sees the whole dependency structure) — and it is the one
    // boundary EVERY re-entry, draft or reassemble, must cross.
    ...lintIsolatedLemmas(paperSafe),
    ...refProblems,
  ];
  if (problems.length > 0) {
    throw new Error(
      `P2 paper lint failed: ${problems.map((p) => `${p.gate}: ${p.detail}`).join("; ")}`,
    );
  }
  await writeFile(join(io.outDir, "paper.tex"), paperSafe + "\n", "utf8");
  await recordP2Assembly(io.outDir);
}

/**
 * Every rendered proof must actually reach the assembled paper.
 *
 * Placement is spread across several filters (main results into the deferred-proofs appendix,
 * appendix-placed lemmas inline after their env, body-placed lemmas behind a pointer). A result
 * whose env kind matched none of them was rendered into `proofs/<id>.tex`, audited, and then
 * silently dropped: `propositionv` did exactly that, and four `lemmav`/`theoremv` proofs in shipped
 * bundles are missing for a still-unidentified reason. No lint noticed, because every check ran on
 * what the paper CONTAINS rather than on what the stage PRODUCED. This compares the two.
 *
 * Exported for tests.
 */
export function lintProofsReachedPaper(paperTex: string, renderedProofIds: Iterable<string>): LintProblem[] {
  const problems: LintProblem[] = [];
  for (const objId of renderedProofIds) {
    if (!paperTex.includes(`\\begin{proof}[Proof of \\cref{obj:${objId}}]`)) {
      problems.push({
        gate: "proof-dropped",
        objId,
        detail: `${objId}: a proof was rendered and audited for this result but never placed in paper.tex — the reader sees the statement with no proof`,
      });
    }
  }
  return problems;
}

/** Env kinds carrying a MAIN result, i.e. one whose proof is rendered individually, audited at
 *  high effort, and placed in the deferred-proofs appendix. `propositionv` belongs here: it was
 *  omitted from every proof path, so a result presented as a Proposition silently shipped with no
 *  proof rendered, none audited, and none in the paper — even with a verified Lean declaration. */
export function isMainProofEnv(env: string): boolean {
  return env === "theoremv" || env === "propositionv";
}

export { canonicalizeProofTitle };

/** Parse a complete proof block from the first draft or an applied repair. */
export function parseProofRender(stdout: string, objId: string): string | null {
  if (/^\s*UNCLEAR:/m.test(stdout)) return null;
  const proof = extractBalancedEnv(stdout, "proof");
  return proof ? canonicalizeProofTitle(objId, normalizeCrefs(proof)) : null;
}

/** Inserts each lemma proof directly after its \end{lemmav} block. Exported
 *  for tests. */
export function insertLemmaProofs(tex: string, proofs: Map<string, string>): string {
  return tex.replace(
    /\\begin\{lemmav\}\{([\w:-]+)\}(\[[^\]]*\])?[\s\S]*?\\end\{lemmav\}/g, // obj_id may contain ':'
    (envBlock, objId: string) => {
      const proof = proofs.get(objId);
      return proof ? `${envBlock}\n\n${proof}` : envBlock;
    },
  );
}

/** Appends a "proof deferred" pointer after each BODY lemma's \end{lemmav} block (for the ids in
 *  `lemmaIds`, whose proofs live in the consolidated proofs appendix labelled `sectionLabel`).
 *  Without it a body-placed lemma would print statement-only, with its proof nowhere. Exported
 *  for tests. */
export function insertProofPointers(tex: string, lemmaIds: Set<string>, sectionLabel: string): string {
  return tex.replace(
    /\\begin\{lemmav\}\{([\w:-]+)\}(\[[^\]]*\])?[\s\S]*?\\end\{lemmav\}/g,
    (envBlock, objId: string) =>
      lemmaIds.has(objId)
        ? `${envBlock}\n\nThe proof is deferred to \\cref{${sectionLabel}}.`
        : envBlock,
  );
}

function validatePlacement(outline: Outline, envs: AnchoredEnv[]): void {
  const placed = outline.sections.flatMap((s) => s.objs);
  const placedSet = new Set(placed);
  const envIds = new Set(envs.map((e) => e.obj_id));
  const missing = [...envIds].filter((id) => !placedSet.has(id));
  const unknown = placed.filter((id) => !envIds.has(id));
  const dupes = placed.filter((id, i) => placed.indexOf(id) !== i);
  if (missing.length || unknown.length || dupes.length) {
    throw new Error(
      `P2 outline placement invalid — missing: [${missing.join(", ")}], unknown: [${unknown.join(", ")}], duplicated: [${dupes.join(", ")}]`,
    );
  }
}

/** Repair only the exact named passages. Invalid/ambiguous patches leave the saved proof
 * untouched; the audit loop records the stopped attempt instead of buying another rewrite. */
export function parseProofRepair(stdout: string, priorProof: string): string | null {
  let parsed: { replacements?: unknown } | null;
  const json = /^```(?:json)?\s*\n([\s\S]*?)\n```\s*$/.exec(stdout.trim())?.[1] ?? stdout.trim();
  try { parsed = JSON.parse(normalizeRawModelJson(json)); repairLatexStringsDeep(parsed); } catch { return null; }
  if (!parsed || !Array.isArray(parsed.replacements)) return null;
  const opening = "\\begin{proof}", closing = "\\end{proof}";
  if (!priorProof.startsWith(opening) || !priorProof.endsWith(closing)) return null;
  const { end: bodyStart } = readOptionalTitle(priorProof, opening.length);
  const replacements: TextReplacement[] = [];
  for (const patch of parsed.replacements) {
    if (!patch || typeof patch.before !== "string" || !patch.before || typeof patch.after !== "string") return null;
    if (/\\(?:begin|end)\{proof\}/.test(patch.before + patch.after)) return null;
    replacements.push(patch);
  }
  // Same ordered protocol as prose revisions: a patch can refer to text introduced
  // by an earlier patch. Restrict editing to the body and commit only a complete result.
  const applied = applyTargetedReplacements(priorProof.slice(bodyStart, -closing.length), replacements);
  if (applied.skipped.length > 0) return null;
  const revised = priorProof.slice(0, bodyStart) + applied.tex + closing;
  return extractBalancedEnv(revised, "proof") === revised ? revised : null;
}
