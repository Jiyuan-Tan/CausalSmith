import { mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { join } from "node:path";
import { createHash } from "node:crypto";
import { z } from "zod";
import type { StageIO } from "../pipeline.js";
import { presentationPrompt } from "../prompt_io.js";
import { parseJsonLoose } from "../gates.js";
import { REFEREE_REPLY } from "../reply_schemas.js";
import { reviewerTexFor } from "../tex_anchors.js";
import { bankAcceptedDir } from "../paths.js";
import type { ReviewFinding } from "../revision_brief.js";
import { buildVerificationContract } from "../verification_contract.js";
import { loadBankNarrative } from "../bank.js";
import { findingFingerprint, renderRoutingPlan } from "../revision_routing.js";
import { utcToday } from "../iso_date.js";
import { updateBundleMeta } from "../meta_store.js";
import { MODELS } from "../../models.js";

interface Review {
  /** ISO date (UTC) the referee ran. The site compares it with the paper's `revised` date to
   *  decide whether to show a staleness note; a legacy review lacks it and gets generic wording. */
  reviewed_at: string;
  /** sha256 of the ON-DISK `paper.tex` at review time — the exact value
   *  `meta.json`'s `versions[].paper_sha256` records, so the site can say which version was
   *  reviewed. Note the referee is SENT `refereeTexFor(paperTex)` (a reviewer copy with the
   *  build-only anchors stripped); hashing that instead would produce a digest matching nothing
   *  else in the bundle. */
  manuscript_sha256: string;
  recommendation: "accept" | "minor_revision" | "major_revision" | "reject";
  /** Holistic overall score, 0–10 with one decimal. Advisory (gates nothing). */
  score: number;
  score_rationale: string;
  summary: string;
  strengths: string[];
  findings: ReviewFinding[];
  questions_for_authors: string[];
}

const SEV_ORDER = { major: 0, minor: 1, nit: 2 } as const;

const FindingSchema = z.object({
  severity: z.enum(["major", "minor", "nit"]),
  section: z.string(),
  issue: z.string(),
  fix: z.string(),
  kind: z.enum(["prose", "structure", "statement", "citation", "other"]).default("other"),
  finding_id: z.string().min(1).optional(),
  remedy: z.enum([
    "rewrite",
    "citation_research",
    "new_theorem",
    "simulation",
    "implementation",
    "source_change",
    "adjudication",
  ]).optional(),
});

const ReviewSchema = z.object({
  recommendation: z.enum(["accept", "minor_revision", "major_revision", "reject"]),
  score: z.preprocess((raw) => {
    const score = normalizeScore(raw);
    return score === null ? undefined : score;
  }, z.number()),
  score_rationale: z.string().default(""),
  summary: z.string().default(""),
  strengths: z.array(z.string()).default([]),
  findings: z.array(FindingSchema).default([]),
  questions_for_authors: z.array(z.string()).default([]),
});

/**
 * P5 — submission referee review. Sends the FINAL paper (paper.tex, post-P4
 * latex-fix) to codex as a journal referee. The formal layer is machine-verified
 * (P3), so the referee does not re-derive proofs — it judges contribution, claim
 * fidelity to the verified statements, exposition, clarity, and positioning. The
 * review is returned as structured JSON/Markdown. The pipeline may automatically
 * re-draft safe prose/structure findings, but never statement/citation/source-truth
 * findings; those are routed to an explicit adjudication halt.
 */
/** Back-compat alias: the reviewer-copy strip now lives in `tex_anchors` because the P3
 *  rubric reviewer needs it too (same reasoning — a scorer reads the paper, not the build). */
export const refereeTexFor = reviewerTexFor;

export async function stageP5(io: StageIO): Promise<void> {
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p5.stub"), "dry-run\n");
    return;
  }
  // ONE snapshot, hashed immediately. The referee text, the hash recorded beside the review and
  // the review itself must all describe the SAME bytes. Hashing the file again after the model
  // returns — minutes later — meant that a P4 re-emit landing mid-review stamped the new
  // manuscript's hash onto a review of the old one, which is exactly the claim the field exists
  // to make impossible. Read as bytes so the digest matches `versions[].paper_sha256` exactly.
  const paperBytes = await readFile(join(io.outDir, "paper.tex")).catch(() => null);
  if (paperBytes === null) {
    throw new Error("P5: paper.tex not found — run P4 first (or `--from P4`).");
  }
  const manuscriptSha256 = createHash("sha256").update(paperBytes).digest("hex");
  const paperTex = paperBytes.toString("utf8");
  const reviewedAt = utcToday();
  const relatedWork = await readFile(join(io.outDir, "related_work_brief.md"), "utf8").catch(() => "");
  const readRequiredJson = async (name: string) =>
    JSON.parse(await readFile(join(io.outDir, name), "utf8"));
  const readOptionalJson = async (name: string, fallback: unknown) =>
    JSON.parse(await readFile(join(io.outDir, name), "utf8").catch(() => JSON.stringify(fallback)));
  const verificationContract = buildVerificationContract(
    await readRequiredJson("formal_layer.json"),
    await readRequiredJson("lean_snippets.json"),
    await readOptionalJson("equivalence_cache.json", {}),
    await readOptionalJson("proof_audit_cache.json", {}),
  );
  await writeFile(
    join(io.outDir, "verification_contract.json"),
    JSON.stringify(verificationContract, null, 2) + "\n",
    "utf8",
  );

  // Only the restriction-shaped honest_scope reaches the referee — never the tldr /
  // justification advertisements, which would anchor an independent review to the
  // authors' own framing.
  const narrative = await loadBankNarrative(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec);
  const prompt = await presentationPrompt("p5_review", {
    paper_tex: refereeTexFor(paperTex),
    related_work_brief: relatedWork,
    honest_scope: narrative.honestScope || "(none recorded)",
    verification_contract: JSON.stringify(verificationContract),
  });
  const { stdout } = await io.ctx.deps.runCodex({
    prompt,
    cwd: io.ctx.repoRoot,
    reasoningEffort: "high",
    leanLsp: false,
    model: MODELS.codexPresentationReview,
    outputSchema: REFEREE_REPLY,
  });
  const parsed = parseJsonLoose(stdout);
  const shaped = ReviewSchema.safeParse(parsed);
  if (!shaped.success) {
    throw new Error(`P5: referee returned invalid review JSON: ${shaped.error.message}`); // why: invalid enum/array/score shapes must not be treated as usable review artifacts.
  }
  const review: Review = {
    // Provenance first, so a reader of p5_review.json sees WHAT was reviewed and WHEN before
    // the verdict. The hash is of paper.tex as it sits on disk — the same bytes P4 recorded in
    // `versions[].paper_sha256` — so review and version can be matched exactly.
    reviewed_at: reviewedAt,
    manuscript_sha256: manuscriptSha256,
    ...shaped.data,
    score_rationale: shaped.data.score_rationale.trim(),
    findings: shaped.data.findings
      .map((finding): ReviewFinding => {
        const remedy = finding.remedy ?? (
          finding.kind === "prose" || finding.kind === "structure"
            ? "rewrite"
            : finding.kind === "citation"
              ? "citation_research"
              : finding.kind === "statement"
                ? "source_change"
                : "adjudication"
        );
        return {
          ...finding,
          finding_id: finding.finding_id?.trim() || findingFingerprint(finding),
          remedy,
        };
      })
      .slice()
      .sort((a, b) => (SEV_ORDER[a.severity] ?? 9) - (SEV_ORDER[b.severity] ?? 9)),
  };

  await archivePriorReview(io.outDir);
  await writeFile(join(io.outDir, "p5_review.json"), JSON.stringify(review, null, 2) + "\n", "utf8");
  await writeFile(join(io.outDir, "p5_review.md"), renderReviewMd(review), "utf8");
  // The routing plan (fix by hand / escalate / your call) travels with the review, whatever
  // entry produced it.
  await writeFile(join(io.outDir, "p5_revision_routing.md"), renderRoutingPlan(review), "utf8");

  // Sink 1 — the site's per-paper contract. P4 emits meta.json BEFORE P5 runs, so the score is
  // injected here. Through the shared writer: this used to be its own unlocked whole-file
  // read-modify-write, so a DOI published between P5's read and P5's write was reverted by a
  // stale object that differed from it only in the score. The mutator names only the two keys
  // P5 owns, so nothing else can be lost whatever else is happening to the bundle.
  if (existsSync(join(io.outDir, "meta.json"))) {
    await updateBundleMeta(io.outDir, (meta) => {
      meta.score = review.score;
      meta.score_rationale = review.score_rationale || null;
    });
  } else {
    io.state.notes.push("P5: meta.json absent (P4 not run) — score not injected into the bundle.");
  }

  // Sink 2 — the accepted bank entry, for later topic generation. Targeted
  // replace-or-insert of two frontmatter scalars; leaves every other line intact.
  const bankReadme = join(bankAcceptedDir(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec), "README.md");
  if (existsSync(bankReadme)) {
    const md = await readFile(bankReadme, "utf8");
    const patched = upsertFrontmatter(md, {
      paper_score: String(review.score),
      paper_score_rationale: JSON.stringify(review.score_rationale || ""),
    });
    if (patched !== null) await writeFile(bankReadme, patched, "utf8");
    else io.state.notes.push("P5: bank README has no frontmatter — paper_score not recorded.");
  } else {
    io.state.notes.push("P5: accepted bank README absent — paper_score not recorded.");
  }

  const majors = review.findings.filter((f) => f.severity === "major").length;
  io.state.notes.push(
    `P5: referee recommendation=${review.recommendation}; score=${review.score}/10; ${review.findings.length} findings (${majors} major). See p5_review.md.`,
  );
}

/** Preserve every referee draw before overwriting the live review. Scores are noisy,
 * so revision history must remain auditable rather than retaining only the last or best pass. */
export async function archivePriorReview(outDir: string): Promise<string | null> {
  const json = await readFile(join(outDir, "p5_review.json"), "utf8").catch(() => null);
  if (json === null) return null;
  const md = await readFile(join(outDir, "p5_review.md"), "utf8").catch(() => "");
  const historyDir = join(outDir, "p5_review_history");
  await mkdir(historyDir, { recursive: true });
  const names = await readdir(historyDir);
  const indices = names
    .map((name) => /^round_(\d+)\.json$/.exec(name)?.[1])
    .filter((value): value is string => value !== undefined)
    .map(Number);
  const next = (indices.length > 0 ? Math.max(...indices) + 1 : 0).toString().padStart(3, "0");
  const stem = `round_${next}`;
  await writeFile(join(historyDir, `${stem}.json`), json, "utf8");
  await writeFile(join(historyDir, `${stem}.md`), md, "utf8");
  return stem;
}

/**
 * Coerce the referee's `score` field to a well-formed 0–10 value, one decimal.
 * Returns null when the value is missing, non-numeric, or outside [0,10], so the
 * caller fails the stage instead of silently rewriting the referee's score.
 */
export function normalizeScore(raw: unknown): number | null {
  // `Number(null)` / `Number("")` are 0, so reject non-numeric inputs before coercing.
  const n =
    typeof raw === "number"
      ? raw
      : typeof raw === "string" && raw.trim() !== ""
        ? Number(raw)
        : NaN;
  if (!Number.isFinite(n)) return null;
  if (n < 0 || n > 10) return null;
  return Math.round(n * 10) / 10;
}

/**
 * Replace-or-insert scalar keys in a Markdown YAML frontmatter block. For each
 * key: if a top-level `key: …` line exists, its value is replaced in place;
 * otherwise the pair is inserted just before the closing `---`. Every other line
 * is byte-preserved. Returns null if the document has no `---\n…\n---` block.
 */
export function upsertFrontmatter(md: string, kv: Record<string, string>): string | null {
  if (!md.startsWith("---\n")) return null;
  const end = md.indexOf("\n---", 4);
  if (end < 0) return null;
  const head = md.slice(4, end).split("\n");
  const rest = md.slice(end); // starts with "\n---"
  for (const [key, value] of Object.entries(kv)) {
    const line = `${key}: ${value}`;
    const idx = head.findIndex((l) => new RegExp(`^${key}:(\\s|$)`).test(l));
    if (idx >= 0) head[idx] = line;
    else head.push(line);
  }
  return "---\n" + head.join("\n") + rest;
}

function renderReviewMd(r: Review): string {
  const lines: string[] = [];
  lines.push(
    `# Referee review`,
    ``,
    `**Recommendation:** ${r.recommendation}`,
    `**Overall score:** ${r.score}/10${r.score_rationale ? ` — ${r.score_rationale}` : ""}`,
    ``,
    r.summary,
    ``,
  );
  if (r.strengths.length) {
    lines.push(`## Strengths`, ...r.strengths.map((s) => `- ${s}`), ``);
  }
  if (r.findings.length) {
    lines.push(`## Findings`);
    for (const f of r.findings) {
      lines.push(`- **[${f.severity}·${f.kind ?? "other"}] ${f.section}** — ${f.issue}`, `  - *Fix:* ${f.fix}`);
    }
    lines.push(``);
  }
  if (r.questions_for_authors.length) {
    lines.push(`## Questions for authors`, ...r.questions_for_authors.map((q) => `- ${q}`), ``);
  }
  return lines.join("\n") + "\n";
}
