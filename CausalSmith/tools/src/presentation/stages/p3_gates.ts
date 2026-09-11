import { readFile, writeFile, appendFile, mkdir } from "node:fs/promises";
import { MODELS } from "../../models.js";
import { join } from "node:path";
import type { StageIO } from "../pipeline.js";
import { presentationPrompt, promptFingerprint } from "../prompt_io.js";
import { parseOutline } from "../stage_util.js";
import { CITATION_SUPPORT_REPLY, OVERCLAIM_REPLY, REPLACEMENTS_REPLY, RUBRIC_REPLY } from "../reply_schemas.js";
import { canonicalizeObjRefs, lintAnchors, lintEnvOrder, hashEnvBody, normalizeCrefs, parseAnchoredEnvs, repairObjRefs, reviewerTexFor } from "../tex_anchors.js";
import { FormalLayerSource, blocksToTex } from "../formal_layer.js";
import { applyProseRevision, proofBlocks, applyTargetedReplacements, type TextReplacement } from "../prose_revision.js";
export { applyTargetedReplacements, type TextReplacement } from "../prose_revision.js";
import { assertP2AssemblyFresh, recordP2Assembly, texFilesUnder } from "../assembly_freshness.js";
import { parseBib } from "../citations.js";
import { savePaperState } from "../state.js";
import { writeJsonAtomic } from "../json_io.js";
import { loadJsonCache } from "../cache.js";
import { loadBankNarrative } from "../bank.js";
import { maskNonBoundaryPeriods } from "../../shared/tex_text.js";
import {
  runHardGates,
  gateLoop,
  minRubric,
  parseRubricReview,
  parseJsonLoose,
  GATE_RERUN_SENTINEL,
  type GateRunners,
  type HardGateInput,
  type RubricReview,
} from "../gates.js";

const MAX_ROUNDS = 2;
const RUBRIC_PASS = 6;

/** The frozen presentation env names (must match FormalBlock.env). */
const FROZEN_ENV_NAMES = [
  "theoremv",
  "assumptionv",
  "lemmav",
  "definitionv",
  "citedv",
  "propositionv",
  "remarkv",
  "algorithmv",
] as const;

/**
 * Remove the frozen statement envs from a stretch of section text, leaving the
 * surrounding interpretive PROSE. The overclaim gate audits prose against the
 * frozen claims (supplied separately as `frozenEnvsTex`), so it must NOT see the
 * frozen claims inside the prose too: a frozen env sits in the Discussion/etc.
 * section, and if the gate flags a phrase INSIDE it the reviser cannot fix it
 * (editing a frozen body trips the frozen-layer guard and aborts the round). A
 * frozen statement is the fidelity-gated proved claim itself — not prose that can
 * over- or under-claim — so stripping it here is correct, not a workaround.
 */
function stripFrozenEnvs(tex: string): string {
  let out = tex;
  for (const env of FROZEN_ENV_NAMES) {
    out = out.replace(new RegExp(`\\\\begin\\{${env}\\}[\\s\\S]*?\\\\end\\{${env}\\}`, "g"), "");
  }
  return out;
}

/** Remove full-line LaTeX comments before model-facing prose audits. These lines are
 * not reader-visible claims; provenance markers such as `% DERIVED ...` must not
 * consume a P3 revision round as alleged overclaiming. */
export function stripLatexCommentLines(tex: string): string {
  return tex.replace(/^[ \t]*%.*(?:\r?\n|$)/gm, "");
}

/** Stable prose units for differential overclaim re-review.
 *
 * Split points are computed on a PERIOD-MASKED copy (decimals and `e.g.`-style
 * abbreviations are not boundaries — `see, e.g. \citet{Foo}` used to split) and
 * a boundary is refused when the "next sentence" is really a closing math token
 * (`\[ f(x) = x. \] Hence …` used to yield a bare `\]` unit). The emitted units
 * are sliced from the ORIGINAL collapsed text, never the masked copy. */
export function claimUnits(tex: string): string[] {
  const collapsed = tex.replace(/\s+/g, " ");
  const masked = maskNonBoundaryPeriods(collapsed); // 1:1 char replacement — offsets align
  const parts: string[] = [];
  let start = 0;
  for (const m of masked.matchAll(/(?<=[.!?])\s+(?=(?:\\(?![)\]])(?!end\b)|[A-Z]))/g)) {
    parts.push(collapsed.slice(start, m.index));
    start = m.index! + m[0].length;
  }
  parts.push(collapsed.slice(start));
  return parts.map((s) => s.trim()).filter((s) => /[A-Za-z]/.test(s));
}

function contextualClaimUnits(tex: string): { sentence: string; context: string; ordinal: number }[] {
  const units = claimUnits(tex);
  return units.map((sentence, i) => ({
    sentence,
    ordinal: i,
    context: [units[i - 1] ?? "(start)", sentence, units[i + 1] ?? "(end)"].join("\n"),
  }));
}

/** Return the cached P2 front-matter artifact as it appears in an assembled paper. */
export function frontMatterFromPaper(paperTex: string): string | null {
  const abstract = /\\begin\{abstract\}[\s\S]*?\\end\{abstract\}/.exec(paperTex);
  if (!abstract || abstract.index === undefined) return null;
  const firstSection = /\\section\{([^}]*)\}/g;
  firstSection.lastIndex = abstract.index + abstract[0].length;
  const intro = firstSection.exec(paperTex);
  // The cache is specifically the abstract plus Introduction.  Do not guess
  // when a reviser has renamed or deleted that heading: guessing can swallow a
  // body section and make the next P2 assembly delete the real introduction.
  if (!intro || intro[1] !== "Introduction" || intro.index === undefined) return null;
  const terminator = /\\section\{|\\appendix\b|\\end\{document\}/g;
  terminator.lastIndex = intro.index + intro[0].length;
  const end = terminator.exec(paperTex)?.index ?? paperTex.length;
  // This one contiguous slice deliberately retains every byte between the
  // abstract and Introduction (keywords, JEL lines, framing text, ...).
  return paperTex.slice(abstract.index, end);
}

/** Validate and normalize the P2 cache text derived from an assembled paper. */
export function checkedFrontMatterFromPaper(paperTex: string): string {
  const frontMatter = frontMatterFromPaper(paperTex);
  if (frontMatter === null) {
    throw new Error("P3 front-matter synchronization could not locate an abstract and first section");
  }
  const captured = parseAnchoredEnvs(frontMatter);
  if (captured.length > 0) {
    throw new Error(
      `P3 front-matter synchronization refused an extract containing anchored formal environments: ${captured.map((e) => e.obj_id).join(", ")}`,
    );
  }
  // P2 separates front matter and body with two newlines. Do not retain that
  // separator and append another one on every P2 → P3 cycle.
  return frontMatter.trimEnd() + "\n";
}

/** Select the paragraphs most lexically related to the reported problems. */
export function revisionContext(tex: string, details: string[]): string {
  // P3 edits prose only. Do not select protected proofs as apparent repair targets.
  for (const proof of proofBlocks(tex)) tex = tex.replace(proof, "");
  const terms = new Set(details.join(" ").toLowerCase().match(/[a-z][a-z0-9_-]{3,}/g) ?? []);
  const parts = tex.split(/\n\s*\n/);
  const scored = parts.map((part, i) => ({
    part,
    i,
    score: (part.toLowerCase().match(/[a-z][a-z0-9_-]{3,}/g) ?? []).filter((t) => terms.has(t)).length,
  }));
  const selected = scored
    .filter((x) => x.score > 0)
    .sort((a, b) => b.score - a.score || a.i - b.i)
    .slice(0, 10)
    .sort((a, b) => a.i - b.i)
    .map((x) => x.part);
  return (selected.length > 0 ? selected : parts.slice(0, 6)).join("\n\n");
}

/**
 * P3 — WHOLE-PAPER hard gates (overclaiming, citation pool + support, anchor lint) with a bounded
 * revise loop, then the soft rubric ensemble. The Lean-anchored PER-ARTIFACT audits now run with the
 * stage that produces the artifact: statement equivalence at P1 (judgeStatements, inside the render loop), proof
 * faithfulness at P2 (runProofAudit) — so a failure surfaces at its source rather than being
 * re-discovered here. Codex runs the overclaim gate; opus provides the independent prose review via
 * half the rubric ensemble (opus ×1 + codex ×1), so the prose is scored by a model that did not write
 * it.
 */
export async function stageP3(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p3.stub"), "dry-run\n");
    return;
  }
  const { deps } = io.ctx;
  // `state.revision_round` is a pipeline-wide counter: each P3 revision pass increments it,
  // and prior P3 invocations may already have revised the
  // paper.  P3's two-round budget is per invocation, so never use that durable
  // counter as the local gate-loop cursor.
  let p3RevisionRound = 0;
  /**
   * Persist state, THEN throw.
   *
   * `pipeline.ts` only calls `savePaperState` after a stage returns, so a stage that
   * records a diagnosis and then throws loses it: `hard_gate_failures` was assigned at
   * all three failure exits below and still read `[]` in every run on disk, even when
   * `run_p3.log` showed the equivalence gate failing on 7 statements. The record is
   * the whole point of the field — write it before unwinding.
   */
  const failP3 = async (message: string): Promise<never> => {
    await savePaperState(io.outDir, io.state).catch(() => {}); // never mask the real error
    throw new Error(message);
  };
  const paperPath = join(io.outDir, "paper.tex");
  const frontMatterPath = join(io.outDir, "front_matter.tex");
  // P3 records the assembly after its own validated writes, so it must first prove the sources it
  // starts from ARE the assembled ones: a hand edit since P2 needs a reassembly, not a blessing.
  // A bundle assembled before the manifest existed has nothing to compare against and is left as is
  // (its first P3 write then records a baseline; every live bundle with a paper.tex has a manifest).
  await assertP2AssemblyFresh(io.outDir).catch((err: Error) => {
    if (!/manifest is missing/.test(err.message)) throw err;
  });
  const reviewsPath = join(io.outDir, "logs", "reviews.jsonl");
  await mkdir(join(io.outDir, "logs"), { recursive: true });
  const formalLayer = FormalLayerSource.parse(
    JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")),
  );
  const frozen = new Map<string, string>(formalLayer.blocks.map((b) => [b.obj_id, b.body]));
  const frozenEnvsTex = blocksToTex(formalLayer.blocks); // derived from the source of truth, never the on-disk .tex
  const bibEntries = parseBib(await readFile(join(io.outDir, "references.bib"), "utf8"));
  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8").catch(() => "");
  // The entry's own do-not-claim charter (honest_scope + comparator promises) — a
  // restriction-shaped detector input for the overclaim gate, never authoring context.
  const narrative = await loadBankNarrative(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec);
  const scopeCharter = [
    narrative.honestScope && `Honest-scope charter (claims the research stage itself disclaims):\n${narrative.honestScope}`,
    narrative.comparatorPromises && `Comparator promises (what each cited competitor did and did not establish):\n${narrative.comparatorPromises}`,
  ].filter(Boolean).join("\n\n") || "(none recorded)";
  // P3 protects the complete P1 formal-layer namespace, including presentation-owned setup
  // definitions that intentionally have no bank crosswalk/Lean declaration.
  const known = new Set(frozen.keys());
  const frontMatterOrFail = async (source: string): Promise<string> => {
    try {
      return checkedFrontMatterFromPaper(source);
    } catch {
      return failP3(
        "P3 front-matter synchronization failed: the reviser deleted or renamed the required " +
        "\\section{Introduction} heading; restore that heading before publishing.",
      );
    }
  };
  const syncFrontMatter = async (paperTex?: string): Promise<void> => {
    const source = paperTex ?? await readFile(paperPath, "utf8");
    await writeFile(frontMatterPath, await frontMatterOrFail(source), "utf8");
  };

  // Environment order is structural and P1's alone: P3 prose revision cannot move the frozen
  // environments, so a paper that reorders the layer fails directly instead of burning rounds.
  const layerOrder = formalLayer.blocks.filter((b) => b.env !== null).map((b) => b.obj_id);
  const orderProblems = lintEnvOrder(await readFile(paperPath, "utf8"), layerOrder);
  if (orderProblems.length > 0) {
    io.state.hard_gate_failures = orderProblems;
    await failP3(
      `P3 frozen-layer order gate failed (${orderProblems.map((p) => p.detail).join("; ")}). ` +
        `P2 must lay the sections out in the P1 order; re-run P2, do not restart the presentation run.`,
    );
  }

  // Per-gate verdict cache, content-keyed: P3 is the expensive stage, so a
  // rerun must only re-pay for inputs that actually changed. Same input →
  // same cached verdict (including failures — delete gate_cache.json to
  // force a fresh audit).
  const gateCachePath = join(io.outDir, "gate_cache.json");
  interface GateCache {
    citationSupport: Record<string, { verdict: string; reason?: string }>;
    overclaimUnits: Record<string, { flag: { sentence: string; fix?: string } | null }>;
    rubric: Record<string, RubricReview[]>;
  }
  const gateCache = await loadJsonCache<GateCache>(gateCachePath, {
    defaults: { citationSupport: {}, overclaimUnits: {}, rubric: {} },
  });
  // Atomic: citation-support workers save concurrently under mapLimit, and a plain
  // writeFile racing/crashing mid-write corrupts the cache (next P3 run throws on
  // parse until the operator deletes it and re-pays every cached verdict).
  const saveGateCache = () => writeJsonAtomic(gateCachePath, gateCache);

  const ask = async (out: Promise<string> | Promise<{ stdout: string; stderr: string }>) => {
    const res = await out;
    return parseJsonLoose(typeof res === "string" ? res : res.stdout);
  };

  const runners: GateRunners = {
    overclaim: async (frontMatter, envsTex) => {
      const auditFrontMatter = stripLatexCommentLines(frontMatter);
      const auditEnvsTex = stripLatexCommentLines(envsTex);
      // The scope charter is a monotone tightening input to the detector, so it joins
      // the unit key: a charter change must re-audit every unit.
      const envKey = hashEnvBody(`${auditEnvsTex}|${scopeCharter}`);
      const units = contextualClaimUnits(auditFrontMatter);
      const flags: { sentence: string; fix?: string }[] = [];
      const misses: { id: number; sentence: string; context: string; key: string }[] = [];
      units.forEach(({ sentence, context, ordinal }, id) => {
        // Key on the sentence + its neighbour context, NOT the absolute `ordinal`:
        // with the ordinal in the key, inserting or deleting a single sentence
        // invalidates every later sentence and forces a whole-document re-audit
        // (measured: 6 such full re-audits in one run at ~75-80k chars each).
        void ordinal;
        const key = hashEnvBody(`${sentence}|${context}|${envKey}`);
        const hit = gateCache.overclaimUnits[key];
        if (hit) {
          if (hit.flag) flags.push(hit.flag);
        } else misses.push({ id: id + 1, sentence, context, key });
      });
      if (misses.length === 0) return { clean: flags.length === 0, flags };
      const v = (await ask(
        deps.runCodex({ multiAgent: false, // keep codex sub-agents off in gate audits (concurrent multi-agent deadlocks the daemon)
          prompt: await presentationPrompt("p3_overclaim", {
            front_matter_tex: misses
              .map((m) => `[CLAIM ${m.id}]\nNeighbor context:\n${m.context}\nSentence to classify:\n${m.sentence}`)
              .join("\n\n"),
            frozen_envs: auditEnvsTex,
            scope_charter: scopeCharter,
          }),
          cwd: io.ctx.repoRoot,
          reasoningEffort: "medium",
          outputSchema: OVERCLAIM_REPLY,
          leanLsp: false,
        }),
      )) as { clean?: boolean; flags?: { id?: number; sentence: string; fix?: string }[] } | null;
      if (!v || typeof v.clean !== "boolean" || !Array.isArray(v.flags)) {
        return {
          clean: false,
          flags: [{ sentence: misses[0].sentence, fix: `${GATE_RERUN_SENTINEL} Overclaim auditor returned invalid JSON; re-run the gate.` }],
        };
      }
      let matchedFlags = 0;
      const pending: { key: string; flag: { sentence: string; fix?: string } | null }[] = [];
      for (const miss of misses) {
        const flagged = v.flags.find((f) =>
          f.id === miss.id || (f.sentence ?? "").replace(/^\[CLAIM \d+\]\s*/, "").trim() === miss.sentence,
        );
        const flag = flagged ? { sentence: miss.sentence, fix: flagged.fix } : null;
        if (flagged) matchedFlags += 1;
        pending.push({ key: miss.key, flag });
        if (flag) flags.push(flag);
      }
      // Only commit to cache once we know the response was usable. Caching inside the
      // loop above poisoned the cache when the auditor reported an overclaim we could
      // not match: every unit was stored `flag: null`, so the "re-run the gate" retry
      // then hit an all-clean cache and the gate passed vacuously with zero model calls.
      if (v.clean || matchedFlags > 0) {
        // A PARTIALLY-matched reply (some flags matched, others matched no unit) must not
        // cache the un-flagged units as clean: one of them is likely the unmatched flag's
        // real target (id wrong + sentence rephrased), and a cached `flag: null` replays
        // as a clean verdict forever. Cache matched flags; leave clean-LOOKING units
        // uncached for re-audit whenever any flag went unmatched (audit, 2026-08-26).
        const unmatched = v.flags.length - matchedFlags;
        for (const p of pending) {
          if (p.flag === null && unmatched > 0) continue;
          gateCache.overclaimUnits[p.key] = { flag: p.flag };
        }
        if (unmatched > 0) {
          io.state.notes.push(`P3 overclaim: ${unmatched} auditor flag(s) matched no audited sentence — clean-looking units left uncached for re-audit`);
        }
      }
      if (!v.clean && matchedFlags === 0) {
        return {
          clean: false,
          flags: [{ sentence: misses[0].sentence, fix: `${GATE_RERUN_SENTINEL} Auditor reported an unmatched overclaim; re-run the gate.` }],
        };
      }
      const out = { clean: flags.length === 0, flags };
      await saveGateCache();
      return out;
    },
    citationSupportBatch: async (pairs) => {
      // Cost economy: ~10 (sentence, citation) pairs per low-effort codex call; verdicts cached
      // per pair. This is the ONLY citation-support path (singleton groups included). A pair the
      // first pass leaves verdict-less gets ONE in-run retry (see runGroups below); only after
      // that is it reported advisory `unverifiable` by the caller — uncached, so a re-run retries.
      const out = new Map<
        string,
        { verdict: "supported" | "unsupported" | "unverifiable"; reason?: string }
      >();
      const citationKey = (p: typeof pairs[number]) =>
        hashEnvBody([
          p.sentence,
          p.entry.key,
          p.entry.fields.title ?? "",
          p.entry.fields.author ?? "",
          p.entry.fields.year ?? "",
          p.entry.fields.abstract ?? p.entry.fields.note ?? "",
          hashEnvBody(brief),
        ].join("§")); // why: citation prompt depends on bib metadata and related-work context.
      const misses: typeof pairs = [];
      for (const p of pairs) {
        const key = citationKey(p);
        const hit = gateCache.citationSupport[key];
        if (hit) out.set(`${p.entry.key}|${p.sentence}`, hit as never);
        else misses.push(p);
      }
      const CBATCH = 10;
      const runGroups = async (pending: typeof pairs): Promise<typeof pairs> => {
        for (let i = 0; i < pending.length; i += CBATCH) {
          const group = pending.slice(i, i + CBATCH);
          const items = group
            .map(
              (p, j) =>
                `[${j + 1}] sentence: ${p.sentence}\n    cited work (${p.entry.key}): ${p.entry.fields.title ?? ""} — ${p.entry.fields.author ?? ""} (${p.entry.fields.year ?? ""})\n    abstract/notes: ${(p.entry.fields.abstract ?? p.entry.fields.note ?? "").slice(0, 600)}`,
            )
            .join("\n\n");
          try {
            const parsed = (await ask(
              deps.runCodex({ multiAgent: false, // keep codex sub-agents off in gate audits (concurrent multi-agent deadlocks the daemon)
                model: MODELS.codexCitationSupport,
                prompt: await presentationPrompt("p3_citation_support_batch", {
                  items_block: items,
                  related_work_brief: brief,
                }),
                cwd: io.ctx.repoRoot,
                reasoningEffort: "low",
                leanLsp: false,
                outputSchema: CITATION_SUPPORT_REPLY,
              }),
            )) as { results?: { id?: number; verdict?: string; reason?: string }[] } | null;
            for (const r of parsed?.results ?? []) {
              const p = typeof r.id === "number" ? group[r.id - 1] : undefined;
              if (!p) continue;
              if (r.verdict === "supported" || r.verdict === "unsupported" || r.verdict === "unverifiable") {
                const v: { verdict: "supported" | "unsupported" | "unverifiable"; reason?: string } = {
                  verdict: r.verdict,
                  reason: r.reason,
                };
                out.set(`${p.entry.key}|${p.sentence}`, v);
                gateCache.citationSupport[citationKey(p)] = v;
              }
            }
          } catch {
            /* leave the group verdict-less; the retry pass below re-asks it */
          }
        }
        return pending.filter((p) => !out.has(`${p.entry.key}|${p.sentence}`));
      };
      // One retry pass over whatever the first pass left verdict-less (a failed or unparseable
      // batch call must not downgrade a whole group to advisory in one shot — the retry restores
      // the in-run second chance the old per-pair fallback provided). Pairs still verdict-less
      // after the retry are reported advisory `unverifiable` by the caller and stay uncached.
      const unresolved = await runGroups(misses);
      if (unresolved.length > 0) await runGroups(unresolved);
      // Persist before returning: without this the batch verdicts live only in
      // memory, so a later hard-gate throw loses the whole batch and the next
      // round re-pays byte-identical calls (measured: 90 wasted calls in one run).
      if (misses.length > 0) await saveGateCache();
      return out;
    },
  };

  const buildInput = async (): Promise<HardGateInput> => {
    let paperTex = await readFile(paperPath, "utf8");
    const refRepair = repairObjRefs(paperTex, new Set(parseAnchoredEnvs(paperTex).map((e) => e.obj_id)));
    if (refRepair.tex !== paperTex) {
      // why: P3 applies unique obj-ref repairs before lint/audit — BUT a `\ref` inside a FROZEN env
      // body must never be rewritten (that persists frozen-drift the lint would reject). Only write the
      // repair if it leaves every anchored env body byte-identical; otherwise skip and let the
      // downstream ref lint surface it (pre-fix behavior) rather than corrupting a frozen statement.
      const beforeBodies = new Map(parseAnchoredEnvs(paperTex).map((e) => [e.obj_id, hashEnvBody(e.body)]));
      const frozenTouched = parseAnchoredEnvs(refRepair.tex).some(
        (e) => beforeBodies.has(e.obj_id) && beforeBodies.get(e.obj_id) !== hashEnvBody(e.body),
      );
      if (!frozenTouched) {
        paperTex = refRepair.tex;
        // Keep paper.tex and P2's cache synchronized immediately. There is no
        // deferred text state for later gates or the rubric to disagree about.
        const repairedFrontMatter = await frontMatterOrFail(paperTex);
        await writeFile(paperPath, paperTex, "utf8");
        await writeFile(frontMatterPath, repairedFrontMatter, "utf8");
        await recordP2Assembly(io.outDir);
      }
    }
    const cachedFrontMatter = frontMatterFromPaper(paperTex) ?? "";
    // Interpretive body sections carry the comparative / qualitative claims
    // (monotonicity, phase behavior, "free lunch") the overclaim gate must see —
    // the abstract/intro can be correct while a discussion aside contradicts the
    // proved rate. Include discussion/conclusion/extensions/interpretation.
    const interpretive = [
      ...paperTex.matchAll(
        /\\section\{[^}]*(?:Discussion|Conclusion|Extensions?|Interpretation)[^}]*\}[\s\S]*?(?=\\section\{|\\appendix|\\end\{document\}|$)/g,
      ),
    ]
      .map((m) => m[0])
      .join("\n\n");
    // Strip frozen envs from the prose the overclaim gate audits: it compares
    // interpretive prose against the frozen claims (passed separately as
    // `frozenEnvsTex`), and a frozen env flagged inside the prose is unfixable by
    // the reviser (it would trip the frozen-layer guard and abort the round).
    const frontMatter = stripFrozenEnvs(`${cachedFrontMatter}\n\n${interpretive}`);
    const input: HardGateInput = {
      paperTex,
      layerOrder,
      knownObjIds: known,
      frozenBodies: frozen,
      frontMatter,
      frozenEnvsTex,
      bibEntries,
    };
    return input;
  };

  // NOTE: statement equivalence (vs Lean) runs at P1 (judgeStatements) and proof equivalence
  // at P2 (runProofAudit) — each co-located with the stage that produces the artifact. P3 keeps only
  // the WHOLE-PAPER gates below (overclaim, citation pool + support, anchor lint, rubric).

  // Revision is a bounded exact-replacement patch over only the relevant prose
  // paragraphs. The model never receives or rewrites the full paper.
  /** P3 cannot edit frozen statement environments, so a finding whose only proposed action
   *  is to delete or rewrite a synthesized definition is not prose-repairable. Callers must
   *  check this BEFORE dispatching a revision: `revise` throws when nothing survives. */
  const isProseRepairable = (p: { detail: string }): boolean =>
    !/Definitions?\s+(?:~?\\(?:Cref|cref|ref)\{obj:)?synth[_:{0-9-]/i.test(p.detail);

  const revise = async (problems: { gate: string; detail: string }[], round: number, advisory = false) => {
    const before = await readFile(paperPath, "utf8");
    const beforeProofs = proofBlocks(before);
    // P3 cannot edit frozen statement environments. Do not show them to the
    // prose reviser, and omit rubric requests whose only proposed action is to
    // delete or rewrite synthesized definitions.
    const proseProblems = problems.filter(isProseRepairable).filter((p) => !p.detail.includes(GATE_RERUN_SENTINEL));
    if (proseProblems.length === 0) {
      if (problems.some((p) => p.detail.includes(GATE_RERUN_SENTINEL))) {
        return; // nothing to edit — the sentinel only exists so gateLoop re-runs the gate
      }
      throw new Error(`P3 revision round ${round} has no prose-repairable findings`);
    }
    const { stdout } = await deps.runCodex({
      multiAgent: false, // P3
      prompt: await presentationPrompt("p3_revision_patch", {
        problems: proseProblems.map((p) => `- [${p.gate}] ${p.detail}`).join("\n"),
        paper_excerpt: revisionContext(stripFrozenEnvs(before), proseProblems.map((p) => p.detail)),
      }),
      cwd: io.ctx.repoRoot,
      reasoningEffort: "high",
      leanLsp: false,
      outputSchema: REPLACEMENTS_REPLY,
    });
    const parsed = parseJsonLoose(stdout) as { replacements?: TextReplacement[] } | null;
    if (!Array.isArray(parsed?.replacements)) {
      // An advisory repair (rubric) never fails the stage on a malformed reply: the paper stands.
      if (advisory) {
        io.state.notes.push(`P3 advisory revision round ${round}: reviser reply was not a replacements list — nothing applied`);
        return false;
      }
      throw new Error(`P3 revision round ${round} returned no replacements`);
    }
    if (!advisory && parsed.replacements.length === 0) {
      throw new Error(`P3 revision round ${round} returned no replacements`);
    }
    // The reviser's patches cross the model boundary here: a `\cref{obj:…}` it echoed with the
    // prefix dropped, a bare id, or a `\ref`/manual kind are canonicalized on both sides (the
    // paper itself is canonical, so a raw `before` would match nothing and be skipped as missing).
    for (const r of parsed.replacements) {
      if (typeof r.before === "string") r.before = canonicalizeObjRefs(r.before, known);
      if (typeof r.after === "string") r.after = canonicalizeObjRefs(normalizeCrefs(r.after), known);
    }
    const { tex: agentRevision, skipped, applied } = applyTargetedReplacements(before, parsed.replacements,
      // Reject each protected edit before persistence/propagation. Restoring only the final
      // paper would still let a mixed prose/proof response alter the authored proof files.
      (candidate, current) => {
        try {
          return applyProseRevision({
            before: current, revised: candidate, blocks: formalLayer.blocks,
            auditedProofs: beforeProofs, who: `P3 revision round ${round}`,
          }) === candidate;
        } catch {
          return false; // a structurally invalid patch is skipped as protected, never the whole round
        }
      });
    if (skipped.length > 0) {
      io.state.notes.push(
        `P3 revision round ${round}: ${skipped.length} of ${parsed.replacements.length} patch(es) skipped ` +
          `(${skipped.map((k) => `${k.reason}: ${k.before.slice(0, 60)}`).join("; ")}) — the rest applied`,
      );
    }
    if (!advisory && skipped.length === parsed.replacements.length) {
      throw new Error(`P3 revision round ${round}: every patch was missing, non-unique, or protected in paper.tex — nothing applied`);
    }
    // The revision model owns prose, never the P1-frozen formal layer or the P2-audited proofs —
    // the shared applicator re-imposes both mechanically and throws on structural change. Restore
    // runs before the no-change check: when P1 was re-audited after a Lean move, canonical
    // resynchronization may be the only required edit and the prose agent is correct to leave the
    // frozen block alone.
    const revised = applyProseRevision({
      before,
      revised: agentRevision,
      blocks: formalLayer.blocks,
      auditedProofs: beforeProofs,
      who: `P3 revision round ${round}`,
    });
    if (revised === before) {
      if (advisory) {
        io.state.notes.push(`P3 rubric revision round ${round}: no editable prose change; unresolved findings retained for operator/P5 review.`);
        return false;
      }
      throw new Error(`P3 revision round ${round} made no changes to paper.tex`);
    }
    const lint = [...lintAnchors(revised, known, frozen), ...lintEnvOrder(revised, layerOrder)];
    if (lint.length > 0) {
      if (advisory) { // an advisory repair never fails the stage: nothing was written
        io.state.notes.push(`P3 advisory revision round ${round} discarded — it broke the frozen layer: ${lint.map((p) => p.detail).join("; ")}`);
        return false;
      }
      throw new Error(
        `P3 revision round ${round} broke the frozen layer (restored): ${lint.map((p) => p.detail).join("; ")}`,
      );
    }
    // P3 patches paper.tex, not the P2 cache. Derive the cache from that validated assembled
    // source only after every frozen/proof guard has passed, so later regeneration never reseeds
    // pre-review front matter and frozen environments remain untouched.
    const revisedFrontMatter = advisory ? frontMatterFromPaper(revised) : await frontMatterOrFail(revised);
    if (revisedFrontMatter === null) {
      io.state.notes.push(`P3 advisory revision round ${round} discarded — the revised front matter could not be extracted`);
      return false;
    }
    await writeFile(paperPath, revised, "utf8");
    await writeFile(frontMatterPath, revisedFrontMatter, "utf8");
    await recordP2Assembly(io.outDir);
    // Sources-canonical contract: propagate each applied replacement into the authored
    // section/proof source that carries the same text, so a later P2 reassembly (P5
    // revision cycle, --from P2) does not silently revert this repair. A replacement
    // whose text only exists in assembled form (front matter — synced above — or
    // mechanically inserted proof pointers) matches no source file and is skipped.
    // Only the patches that landed in paper.tex may reach the sources: a patch skipped there
    // (non-unique in the assembled paper) can still be unique inside ONE source file, and
    // propagating it would ship an edit no gate saw.
    const diffed = applied;
    let propagated = false;
    const landedInSource = new Set<string>();
    // Sections only: the accept guard proved no applied patch changed a proof block in paper.tex,
    // so a hit inside proofs/ would be a different occurrence and could only diverge an audited proof.
    for (const rel of await texFilesUnder(io.outDir, ["sections"])) {
      const src = await readFile(rel, "utf8").catch(() => null);
      if (src === null) continue;
      let out = src;
      for (const { before: b, after: a } of diffed) {
        const first = out.indexOf(b);
        if (first < 0 || out.indexOf(b, first + b.length) >= 0) continue; // absent or ambiguous here
        out = out.slice(0, first) + a + out.slice(first + b.length);
        landedInSource.add(b);
      }
      if (out !== src) { await writeFile(rel, out, "utf8"); propagated = true; }
    }
    // A patch that landed in paper.tex but in no authored source is front-matter text (synced
    // above) or a source that already diverged from its assembly; the latter reverts on the next
    // `--from P2` reassembly, so say so at the checkpoint instead of finding out then.
    const unsourced = diffed.filter((r) => !landedInSource.has(r.before) && !revisedFrontMatter.includes(r.after));
    if (unsourced.length > 0) {
      io.state.notes.push(
        `P3 revision round ${round}: ${unsourced.length} patch(es) landed in paper.tex but matched no authored source ` +
          `(a section/proof file diverged from its assembly — a later --from P2 reassembly would revert them): ` +
          unsourced.map((r) => r.before.slice(0, 60)).join(" | "),
      );
    }
    // The propagation just changed files the P4 freshness gate digests against the
    // P2-recorded manifest; re-record so a green P3 revision does not hard-block P4.
    // paper.tex received the same replacements above, so sources↔assembly correspond.
    // Only when the loop actually wrote: an unconditional re-record would BLESS
    // unrelated pre-existing staleness (e.g. a checkpoint-time hand edit P2 never
    // assembled) that the P4 assert exists to catch.
    if (propagated) await recordP2Assembly(io.outDir);
    p3RevisionRound = round;
    io.state.revision_round += 1;
    return true;
  };

  // "citation-unverifiable" is advisory (evidence silent, nothing
  // contradicts): logged for the record, never a hard failure and never fed
  // to revision (it is unfixable by prose edits and would burn rounds).
  const isAdvisory = (p: { gate: string }) => p.gate === "citation-unverifiable";

  const result = await gateLoop({
    maxRounds: MAX_ROUNDS,
    run: async () => {
      const problems = await runHardGates(await buildInput(), runners);
      await appendFile(
        reviewsPath,
        JSON.stringify({ kind: "hard-gates", round: p3RevisionRound, problems }) + "\n",
        "utf8",
      );
      const advisories = problems.filter(isAdvisory);
      if (advisories.length > 0) {
        io.state.notes.push(
          `P3: ${advisories.length} citation-support advisories (unverifiable, not failures) — see logs/reviews.jsonl`,
        );
      }
      return problems.filter((p) => !isAdvisory(p));
    },
    revise: async (problems, round) => { await revise(problems, round); },
  });
  if (!result.ok) {
    io.state.hard_gate_failures = result.problems;
    await failP3(
      `P3 hard gates still failing after ${result.rounds} revision rounds: ` +
        result.problems.map((p) => `[${p.gate}] ${p.detail}`).join("; "),
    );
  }

  // Heal stale P2 caches even when all hard gates pass in round zero; front_matter.tex is in the
  // assembly digest, so every write of it is recorded here.
  await syncFrontMatter();
  await recordP2Assembly(io.outDir);

  // soft rubric ensemble: opus ×1 + codex ×1 (user decision 2026-06-10: the
  // two opus reviews scored near-identically, so the duplicate bought nothing;
  // pass = MIN of the two means, keeping the harsher reviewer binding), cached
  // on the paper content.
  // Scored as a function so the rubric can be RE-SCORED after a revision: without a
  // re-score the threshold is unenforceable (runs shipped at min 4.75/5.0/5.5/5.75).
  // Re-reading paper.tex each time also makes the content-keyed cache do the right
  // thing — an unchanged manuscript re-scores for free, a revised one really re-scores.
  const scoreRubric = async (): Promise<{ reviews: RubricReview[]; minScore: number }> => {
    // The scorer reads the paper, not the build: comments never render and have produced
    // findings against text no reader sees. Key on the STRIPPED copy — it is what the
    // reviewer actually saw, so a comment-only edit correctly reuses the score.
    const paperTex = reviewerTexFor(await readFile(paperPath, "utf8"));
    // Key prefix "final|" is a legacy token from the retired intermediate/final
    // review-mode knob, kept so existing run-dir caches stay warm.
    // The prompt fingerprint is part of the key: widening what the reviewer is ASKED to
    // report (the `defects` sweep) must not read a review cached under the narrower prompt —
    // otherwise the very bundle that motivated the change replays its old reviews, reports
    // zero defects, and silently skips the repair. Costs one re-score sweep per bundle.
    const rubricKey = hashEnvBody(`final|${await promptFingerprint("p3_rubric")}|${paperTex}`);
    // Cache reads bypass the reviewer dispatch, so they must be re-validated: a
    // cache written by pre-fix code can hold string-scored reviews whose mean is
    // NaN (NaN < RUBRIC_PASS is false → silent fail-open). Filter every array
    // read from the cache through parseRubricReview, dropping invalid entries.
    const validReviews = (vs: unknown[] | undefined): RubricReview[] =>
      (vs ?? []).map((v) => parseRubricReview(v)).filter((v): v is RubricReview => v !== null);
    let reviews: RubricReview[];
    const cached = validReviews(gateCache.rubric[rubricKey]);
    if (cached.length > 0) {
      reviews = cached;
    } else {
      const rubricPrompt = await presentationPrompt("p3_rubric", { paper_tex: paperTex });
      reviews = [];
      const rubricRuns = [
        () => deps.runClaude({ prompt: rubricPrompt, model: MODELS.claudeMain, cwd: io.ctx.repoRoot, jsonSchema: RUBRIC_REPLY }),
        () => deps.runCodex({ prompt: rubricPrompt, cwd: io.ctx.repoRoot, reasoningEffort: "medium" as const, leanLsp: false, multiAgent: false, outputSchema: RUBRIC_REPLY }),
      ];
      for (const run of rubricRuns) {
        const v = parseRubricReview(await ask(run()));
        if (v) reviews.push(v);
      }
      if (reviews.length === 0) {
        throw new Error("P3 rubric: no reviewer returned a valid review (scores must be finite numbers) — re-run P3");
      }
      if (reviews.length < rubricRuns.length) {
        // A dropped reviewer silently loosens the min-binds ensemble (the discarded one may
        // have been the harsher); proceed fail-closed on what parsed, but say so and do NOT
        // cache the partial ensemble — the next entry retries both reviewers.
        io.state.notes.push(`P3 rubric: ${rubricRuns.length - reviews.length} of ${rubricRuns.length} reviewer(s) returned unusable output — scored on a partial ensemble this pass, uncached`);
      } else {
        gateCache.rubric[rubricKey] = reviews;
        await saveGateCache();
      }
    }
    await appendFile(reviewsPath, JSON.stringify({ kind: "rubric", reviews }) + "\n", "utf8");
    return { reviews, minScore: minRubric(reviews) };
  };

  // Revision entries (P5 cycle / --from P2 re-entry): hard gates above have already
  // re-audited the changed prose; the P5 referee is the holistic judge of the revision,
  // so the rubric's full-paper re-score (and its internal revise loop) is skipped.
  if (io.revisionCycle) {
    io.state.notes.push("P3: rubric skipped (revision cycle — P5 referee is the holistic judge).");
    return;
  }
  let { reviews, minScore } = await scoreRubric();
  const entryScore = minScore;
  // Two-tier consumption. `defects` are concrete, locatable, mechanically fixable reader-facing
  // faults and are ALWAYS repaired. `weaknesses` are judgment calls: a score below the pass line
  // buys ONE revision pass, and the resulting score is RECORDED, never a stage outcome — two
  // reviewers' mean is a noisy number, and P5's referee re-judges the same paper one stage later;
  // failing P3 on it cost a full P3 (rubric ×2 + repair + re-gate) for a decision P5 re-makes.
  const defectsOf = (rs: RubricReview[]): string[] => [...new Set(rs.flatMap((r) => r.defects))];
  const repairThen = async (problems: { gate: string; detail: string }[], label: string): Promise<void> => {
    if (problems.length === 0) return; // a below-line score with nothing repairable is just recorded
    // The advisory repair edits a paper that already passed the hard gates. Snapshot every file it
    // may touch; if its re-gate fails, the passing paper is restored and the defects are recorded —
    // an advisory score never turns a passing paper into a halted stage.
    const snapshotPaths = [paperPath, frontMatterPath, ...(await texFilesUnder(io.outDir, ["sections"]))];
    const snapshot = new Map(await Promise.all(snapshotPaths.map(async (p) => [p, await readFile(p, "utf8").catch(() => null)] as const)));
    if (await revise(problems, p3RevisionRound + 1, true) === false) return;
    const repairStart = p3RevisionRound;
    const repair = await gateLoop({
      maxRounds: Math.max(0, MAX_ROUNDS - repairStart),
      run: async () => (await runHardGates(await buildInput(), runners)).filter((p) => !isAdvisory(p)),
      revise: async (problems, localRound) => { await revise(problems, repairStart + localRound); },
    });
    if (!repair.ok) {
      for (const [p, text] of snapshot) if (text !== null) await writeFile(p, text, "utf8");
      await recordP2Assembly(io.outDir);
      io.state.notes.push(
        `P3: ${label} was discarded — its re-gate failed after ${repair.rounds} repair round(s) and the passing paper was restored: ` +
          repair.problems.map((p) => `[${p.gate}] ${p.detail}`).join("; "),
      );
      return;
    }
    ({ reviews, minScore } = await scoreRubric());
  };
  // One revision pass at most: a below-line score folds the defects into its weakness revision;
  // a passing score with defects repairs only the defects.
  const defects = defectsOf(reviews).filter((d) => isProseRepairable({ detail: d }));
  if (p3RevisionRound < MAX_ROUNDS) {
    if (minScore < RUBRIC_PASS) {
      await repairThen(
        [...reviews.flatMap((r) => r.weaknesses).map((w) => ({ gate: "rubric", detail: w })), ...defects.map((d) => ({ gate: "rubric-defect", detail: d }))],
        "rubric revision",
      );
    } else if (defects.length > 0) {
      io.state.notes.push(`P3: rubric ${minScore.toFixed(2)} with ${defects.length} reader-facing defect(s) — repairing.`);
      await repairThen(defects.map((d) => ({ gate: "rubric-defect", detail: d })), "defect repair");
    }
  }
  // Whatever the FINAL review still reports as a reader-facing defect is an OPERATOR-level fix
  // (frozen environments, placement/merge), recorded for the checkpoint rather than a stage failure.
  const standingDefects = defectsOf(reviews);
  if (standingDefects.length > 0) {
    io.state.notes.push(
      `P3: ${standingDefects.length} reader-facing defect(s) stand in the final review — likely inside frozen ` +
        `environments or structural (placement/merge), needing operator adjudication or a P1 re-entry: ` +
        standingDefects.map((d) => `• ${d}`).join(" "),
    );
    await appendFile(reviewsPath, JSON.stringify({ kind: "rubric-defects-unrepaired", defects: standingDefects }) + "\n", "utf8");
  }
  io.state.notes.push(
    `P3: rubric min score ${minScore.toFixed(2)}${entryScore !== minScore ? ` (entry ${entryScore.toFixed(2)})` : ""} — ` +
      `advisory (line ${RUBRIC_PASS}); the P5 referee is the holistic judge.`,
  );
}
