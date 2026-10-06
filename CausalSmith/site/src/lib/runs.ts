/**
 * Loader for the "shelved runs" list: every research run banked under
 * `doc/research/_bank/{downgraded,failed}/`. These never became working papers,
 * so each is read from its `run_digest.json` (written by `npm run runs:digest`
 * in tools) rather than from a presentation bundle.
 */
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { renderTexLine } from "./docmd.js";

export type RunTier = "downgraded" | "failed";

/** How far a run got, as the reader-facing ladder (index into `STAGES`). */
export const STAGES = [
  { key: "proposed", label: "Proposed", blurb: "A question was posed; no derivation was completed." },
  { key: "derived", label: "Derived", blurb: "An informal mathematical derivation was written and refereed." },
  { key: "stated", label: "Stated in Lean", blurb: "The statements were written in Lean 4; the proofs were not finished." },
  { key: "proved", label: "Proved in Lean", blurb: "The delivered statements were machine-verified in Lean 4." },
] as const;

/** Why a run stopped — a coarse reading of its banking verdict. */
export const WHY = {
  "below-bar": { label: "Sound, below the novelty bar", blurb: "The mathematics passed review, but the result was judged a smaller advance than the run aimed for." },
  partial: { label: "Main result not proved", blurb: "Supporting results were proved; the main claim stayed open or only partly resolved." },
  refuted: { label: "Claim refuted", blurb: "The central claim turned out false, degenerate, or already known." },
  proposal: { label: "Rejected at proposal review", blurb: "The question itself did not survive proposal review." },
  formalization: { label: "Lack of Lean infrastructure", blurb: "The informal mathematics passed review; the Lean proof stopped on prerequisites the Lean libraries do not yet have, or outgrew the effort allowed." },
  other: { label: "Other", blurb: "Stopped for a reason outside the categories above." },
} as const;
export type WhyKey = keyof typeof WHY;

/** Paper type: how the proposed contribution relates to the existing literature. */
export const PAPER_TYPES = {
  gap: { label: "Gap filling", blurb: "Finishes a question that earlier work left open, in that work's own setting." },
  relax: { label: "Assumption relaxation", blurb: "Re-establishes a known kind of result under weaker or dropped assumptions." },
  extend: { label: "New setting", blurb: "Carries a known result or method to a different data structure, design, or estimand." },
  sharpen: { label: "Sharper bound", blurb: "Tightens the rate, constant, or bound of a known result." },
  characterize: { label: "Exact characterization", blurb: "A necessary-and-sufficient condition or complete frontier for a newly posed problem." },
  impossibility: { label: "Impossibility", blurb: "The headline is negative: something cannot be identified or achieved." },
  method: { label: "New method", blurb: "A new estimator, test, design, or algorithm with guarantees." },
  unify: { label: "Unification", blurb: "An equivalence between, or common framework over, existing approaches." },
  other: { label: "Other", blurb: "A contribution that fits none of the types above." },
} as const;
export type PaperType = keyof typeof PAPER_TYPES;

/** Result shape, from the proposal's motif code. */
const SHAPES: Record<string, string> = {
  M1: "Estimand characterization",
  M2: "Estimator equivalence",
  M3: "Sensitivity analysis",
  M4: "Identified set (linear program)",
  M5: "Panel spectral methods",
  M6: "Necessary-and-sufficient identification",
  M7: "Sharpness over a model class",
  M8: "Estimation and inference",
  M9: "Bunching / kink identification",
  M10: "Sharp partial identification",
  M11: "Rate / efficiency frontier",
  M12: "Design-based inference",
  M13: "Optimal experimental design",
  M14: "Adaptive experiments",
  M15: "Network / spatial inference",
  M16: "Policy-learning regret",
  M17: "Conformal / permutation inference",
  M18: "Causal structure identification",
  M19: "Graphical effect identification",
  M20: "Graphical bounds",
};
/** Motifs that modify another shape rather than name one; used only as a fallback. */
const MODIFIER_MOTIFS = new Set(["M7", "M8"]);

const CLUSTERS: Record<string, string> = {
  stat: "Stat",
  exp: "Experimentation",
  pid: "PartialID",
  eid: "ExactID",
  scm: "SCM",
  panel: "Panel",
};

export interface RunRow {
  id: string;
  tier: RunTier;
  cluster: string;
  title: string;
  date: string;
  /** Index into `STAGES`. */
  stage: number;
  why: WhyKey;
  type: PaperType | null;
  shape: string | null;
  target: string | null;
  achieved: string | null;
  /** Statement counts from the derivation core, when one exists. */
  proved: number;
  open: number;
  /** One-sentence banking verdict, rendered. */
  reason: string;
  /** Plain text for the search box. */
  text: string;
}

export interface RunDetail {
  id: string;
  tldr: string | null;
  gap: string | null;
  fill: string | null;
  gapReasons: string[];
  epitaph: string | null;
  status: string | null;
  leanDir: string | null;
  /** The run's raw record (logs, derivation, reviews) as one archive; the repository holds only the digest. */
  archiveUrl: string | null;
}

export function bankRoot(): string {
  return resolve(import.meta.dirname, "..", "..", "..", "doc", "research", "_bank");
}

function readJson(path: string): any {
  try {
    return JSON.parse(readFileSync(path, "utf8"));
  } catch {
    return null;
  }
}

/** Machine paths have no meaning to a reader and must not reach the page. */
function scrub(s: string): string {
  return s
    .replace(/\s*\S*\/(home|Users)\/\S+/g, "")
    .replace(/(^|\s)\/[\w.-]+(\/[\w.-]+){2,}\S*/g, "$1")
    .trim();
}

function tex(s: string | null | undefined): string | null {
  if (typeof s !== "string" || s.trim() === "" || /^TODO\b/.test(s.trim())) return null;
  const clean = scrub(s);
  try {
    return renderTexLine(clean);
  } catch {
    return clean.replace(/&/g, "&amp;").replace(/</g, "&lt;");
  }
}

function titleOf(qid: string): string {
  const words = qid.split("_").slice(1);
  if (words.length === 0) return qid;
  const s = words.join(" ");
  return s.charAt(0).toUpperCase() + s.slice(1);
}

function shapeOf(motifs: Record<string, number>): string | null {
  const ranked = Object.entries(motifs).filter(([c]) => SHAPES[c]).sort((x, y) => y[1] - x[1]);
  const pick = ranked.find(([c]) => !MODIFIER_MOTIFS.has(c)) ?? ranked[0];
  return pick ? SHAPES[pick[0]] : null;
}

/** Stages 1 and 1.5 are the natural-language formalization plan, so Lean begins at stage 2. */
function stageOf(raw: unknown, hasDerivation: boolean): number {
  const n = raw === null || raw === undefined || raw === "" ? NaN : Number(raw);
  if (n >= 5) return 3;
  if (n >= 2) return 2;
  return n >= 0 || hasDerivation ? 1 : 0;
}

function whyOf(reason: string, stage: number, proposalVerdict: string): WhyKey {
  const belowBar = /below|floor|subfield|incremental|score|novelty|thin/i.test(reason);
  if (stage >= 2 && !belowBar && /substrate|formaliz|\bLean\b|\bF[1-5](\.5)?\b|sorr(y|ies)|proof(-review)? loop|infrastructure/i.test(reason)) {
    return "formalization";
  }
  if (stage === 0 || /^(NO-PASS|REJECT|NONFLAGSHIP-KILL)/.test(proposalVerdict)) return "proposal";
  if (/refut|counterexample|\b(is|are|was) false\b|false under|degenerate|collaps|does not exist|duplicate|already known|subsumed/i.test(reason)) {
    return "refuted";
  }
  if (/unresolved|unmatched|bracket|\bopen\b|not proved|unproved|substitut|laundering|undetermined|incomplete|undelivered|not delivered|leav(es|ing)|not determine|\bgap\b|promised|requires|retains/i.test(reason)) {
    return "partial";
  }
  if (belowBar) return "below-bar";
  return "other";
}

const STATUS_NOTE: Record<string, string> = {
  "re-raise": "The mathematics is sound; the result could be re-posed at a more modest scope.",
  retry: "Not refuted — a stronger attempt at the same question is still open.",
  "true-negative": "Treated as a settled negative: the central claim does not hold as posed.",
};

interface Loaded {
  rows: RunRow[];
  details: Map<string, RunDetail>;
}
let cache: Loaded | null = null;

export function loadRuns(root: string = bankRoot()): Loaded {
  if (cache) return cache;
  const rows: RunRow[] = [];
  const details = new Map<string, RunDetail>();
  for (const tier of ["downgraded", "failed"] as const) {
    const tierDir = join(root, tier);
    if (!existsSync(tierDir)) continue;
    for (const id of readdirSync(tierDir).sort()) {
      const d = readJson(join(tierDir, id, "run_digest.json"));
      if (!d) continue;
      const gapReasons: string[] = Array.isArray(d.gap_reasons) ? d.gap_reasons : [];
      const reviewed = typeof d.tier_at_derivation === "string" && !/^(NA|$)/.test(d.tier_at_derivation);
      const stage = stageOf(d.stage_completed, !!d.has_derivation || !!d.has_core || reviewed);
      const reasonRaw: string = d.banked_reason ?? gapReasons[0] ?? "";
      const qid: string = d.qid ?? id;

      rows.push({
        id,
        tier,
        cluster: CLUSTERS[id.split("_")[0]] ?? "Other",
        title: d.title ?? titleOf(qid),
        date: String(d.banked_on ?? "").slice(0, 10),
        stage,
        why: d.stop_reason in WHY ? (d.stop_reason as WhyKey) : whyOf(reasonRaw, stage, d.tier_at_proposal ?? ""),
        type: d.paper_type in PAPER_TYPES ? (d.paper_type as PaperType) : null,
        shape: shapeOf(d.motifs ?? {}),
        target: d.novelty_target ?? null,
        achieved: d.banked_novelty_tier ?? null,
        proved: d.statements?.proved ?? 0,
        open: d.statements?.open ?? 0,
        reason: tex(reasonRaw) ?? "",
        text: `${qid.replace(/_/g, " ")} ${reasonRaw} ${d.tldr ?? ""}`.toLowerCase().slice(0, 900),
      });
      details.set(id, {
        id,
        tldr: tex(d.tldr),
        gap: tex(d.gap),
        fill: tex(d.fill),
        gapReasons: gapReasons.map((g) => tex(g) ?? "").filter(Boolean),
        epitaph: tex(d.proof_attempt_summary),
        status: STATUS_NOTE[d.reraise_status] ?? null,
        // Linked only when the Lean directory is in the tree the site is built from.
        leanDir: typeof d.lean_subdir === "string" && stage >= 2 && existsSync(resolve(root, "..", "..", "..", d.lean_subdir)) ? d.lean_subdir : null,
        archiveUrl: typeof d.archive_url === "string" && /^https:\/\//.test(d.archive_url) ? d.archive_url : null,
      });
    }
  }
  rows.sort((a, b) => b.date.localeCompare(a.date) || a.id.localeCompare(b.id));
  cache = { rows, details };
  return cache;
}
