// tex↔Lean crosswalk: deterministic anchors + reviewer-verdict merge +
// drift→finding folding. Design: code owns anchors (LLMs are unreliable at line
// numbers, which the paper↔Lean click-to-jump view needs); the reviewer owns only
// the semantic drift verdict, keyed by obj_id. `buildCompleteCrosswalkFromGraph`
// is the F5 builder: one row per content node of the formalization graph
// (definition / assumption / theorem / lemma) with line numbers re-stamped from
// the final files — the complete tex↔Lean correspondence backbone for the
// visualization (descriptive, not a gate: F3 restructuring makes paper↔Lean
// lemmas many-to-many).

import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import type { CrosswalkEntry, CrosswalkVerdict } from "../types.js";
import { isUndeliveredNode, type FormalizationGraph } from "../graph/types.js";
import { parseAllDecls } from "./crosswalk_parse.js";

export * from "./crosswalk_parse.js";
export * from "./crosswalk_semantics.js";


/** Verdicts that ASSERT the paper object was verified to MATCH a Lean decl. A
 *  `lean: null` anchor under one of these is contradictory — equivalence
 *  verified against nothing — the cheap invariant that catches a stale or
 *  disconnected anchor (`unmatched` is the honest verdict for a genuinely
 *  unanchored paper object, so it is NOT in this set). */
export const VERIFIED_MATCH_VERDICTS = new Set<CrosswalkVerdict>(["equivalent"]);

/** Self-consistency lint: entries whose verdict claims a verified Lean match but
 *  carry no anchor. A consumer's equivalence gate SKIPS `lean: null` rows, so such
 *  a row silently opts out of verification while asserting it passed. */
export function crosswalkVerifiedWithoutAnchor(entries: CrosswalkEntry[]): CrosswalkEntry[] {
  return entries.filter((e) => e.lean == null && VERIFIED_MATCH_VERDICTS.has(e.verdict));
}

/** One obj_id whose Lean anchor changed between a prior table and a fresh rescan. */
export interface AnchorDrift {
  obj_id: string;
  priorDecl: string | null;
  freshDecl: string | null;
  verdict: CrosswalkVerdict;
}

/** Anchor drift between a prior table (whose verdicts were assigned against ITS
 *  anchors) and a freshly-scanned skeleton of the SAME, now-restructured Lean. A
 *  row whose Lean decl changed (gained / lost / retargeted) has a verdict that is
 *  no longer verified against its current anchor. obj_ids absent from `fresh` are
 *  paper-only (legitimately unanchored) and are not compared. */
export function anchorDriftFindings(
  prior: CrosswalkEntry[],
  fresh: CrosswalkEntry[],
): AnchorDrift[] {
  const freshByObj = new Map(fresh.map((e) => [e.obj_id, e.lean?.decl ?? null]));
  const out: AnchorDrift[] = [];
  for (const p of prior) {
    if (!freshByObj.has(p.obj_id)) continue;
    const priorDecl = p.lean?.decl ?? null;
    const freshDecl = freshByObj.get(p.obj_id) ?? null;
    if (priorDecl !== freshDecl) out.push({ obj_id: p.obj_id, priorDecl, freshDecl, verdict: p.verdict });
  }
  return out;
}

/** Stable crosswalk order: P-blocks, then T-blocks, then L-blocks, then `AUX-`
 *  ids, then everything else; numeric within a kind, lexical for AUX. */
export function sortCrosswalkEntries(entries: CrosswalkEntry[]): CrosswalkEntry[] {
  const rank = (id: string) => {
    const m = id.match(/^([PTL])-(\d+)([a-z]?)$/);
    if (m) {
      const kindRank = m[1] === "P" ? 0 : m[1] === "T" ? 1 : 2;
      return [kindRank, Number(m[2]), m[3]] as const;
    }
    if (id.startsWith("AUX-")) return [3, 0, id] as const;
    return [9, 0, ""] as const;
  };
  return [...entries].sort((a, b) => {
    const ra = rank(a.obj_id);
    const rb = rank(b.obj_id);
    return ra[0] - rb[0] || ra[1] - rb[1] || ra[2].localeCompare(rb[2]);
  });
}

const GRAPH_DECL_KIND: Record<string, string> = {
  definition: "def",
  assumption: "structure",
  theorem: "theorem",
  lemma: "lemma",
};

/**
 * Build the complete crosswalk directly from the (core-keyed) formalization graph —
 * the F5 builder. The graph already carries every paper object (NL statement, Lean
 * link from F2/F3 extraction, review verdict) and a causalsmith-compatible `obj_id`
 * alias, so F5 does not parse the `.md`. One row per content node (definition / assumption /
 * theorem / lemma); setup and gate nodes are not crosswalk rows.
 */
export async function buildCompleteCrosswalkFromGraph(graph: FormalizationGraph, leanDir?: string): Promise<CrosswalkEntry[]> {
  const out: CrosswalkEntry[] = [];
  const declLines = new Map<string, number>();
  const shortCount = new Map<string, number>(); // how many decls share a short name within one file
  if (leanDir) {
    for (const d of await parseAllDecls(leanDir)) {
      declLines.set(`${d.file}\0${d.name}`, d.line);
      // why: count by the SHORT (last `.`-segment) name — parseAllDecls may record a decl either short
      // (`same_thm`, inside a namespace block) or dotted (`B.same_thm`), so keying the ambiguity count
      // by the raw name would miss that both share the short name and wrongly treat it as unique.
      const dShort = d.name.includes(".") ? d.name.slice(d.name.lastIndexOf(".") + 1) : d.name;
      const sk = `${d.file}\0${dShort}`;
      shortCount.set(sk, (shortCount.get(sk) ?? 0) + 1);
    }
  }
  const leanAnchor = (file: string, decl: string, declKind: string): NonNullable<CrosswalkEntry["lean"]> | null => {
    // why: graph extraction stores namespaced decls as FULLY-QUALIFIED names (`Foo.t1_thm`) while
    // `parseAllDecls` indexes the SHORT name — real CausalSmith files use namespaces, so fall back to
    // the short name (last `.` segment) so a real local decl still gets its numeric anchor. Use the
    // fallback ONLY when the short name is UNIQUE in that file: an ambiguous short name (two namespaces
    // defining the same short decl in one file) must downgrade to unresolved, not bind to a wrong line.
    const short = decl.includes(".") ? decl.slice(decl.lastIndexOf(".") + 1) : decl;
    const line =
      declLines.get(`${file}\0${decl}`) ??
      (shortCount.get(`${file}\0${short}`) === 1 ? declLines.get(`${file}\0${short}`) : undefined);
    if (line === undefined) return null; // crosswalk lean.line is numeric; unresolved anchors downgrade rather than persist null.
    return {
      file,
      decl,
      decl_kind: declKind,
      line,
    };
  };
  for (const n of graph.nodes) {
    if (!(n.kind === "definition" || n.kind === "assumption" || n.kind === "theorem" || n.kind === "lemma")) continue;
    if (isUndeliveredNode(n)) continue;
    const objId = n.obj_id ?? n.id;
    const title = (n.nl?.statement ?? "").replace(/\s+/g, " ").trim().slice(0, 80) || objId;
    const lean =
      n.lean?.decl_name && n.lean.file !== null
        // why: `file:null` marks plan-reuse/library decls, not checked run-local declarations.
        ? leanAnchor(n.lean.file ?? "Basic.lean", n.lean.decl_name, GRAPH_DECL_KIND[n.kind] ?? "def")
        : null;
    // A row with NO Lean anchor cannot be a VERIFIED match — a `matched` review on an unanchored node
    // (e.g. an agent-introduced assumption standing in for an inline hypothesis like `hε`/`hz0`) was
    // "verified against nothing". Only an anchored node may be `equivalent`; otherwise it is
    // `unmatched` (a real `drift` is preserved). Keeps the crosswalk from ever claiming equivalence
    // against a `lean:null` anchor — the exact contradiction the F5 consistency gate rejects.
    const verdict: CrosswalkVerdict =
      n.review?.status === "drift"
        ? "drift"
        : n.review?.status === "matched" && lean != null
          ? "equivalent"
          : "unmatched";
    out.push({
      obj_id: objId,
      kind: n.kind,
      title,
      tex: { label: objId, line_range: n.nl?.tex_anchor ?? "" },
      lean,
      verdict,
    });
  }
  return sortCrosswalkEntries(out);
}

// ---------------------------------------------------------------------------
// Verdict merge + rendering + finding fold
// ---------------------------------------------------------------------------

/** Human-readable rendering of the crosswalk (sibling of the JSON backbone). */
export function renderCrosswalkMd(entries: CrosswalkEntry[]): string {
  const lines: string[] = [
    "# tex↔Lean crosswalk",
    "",
    "Definition/assumption/theorem (and, in the F5 complete table, lemma)",
    "correspondence. Durable anchors: `obj_id` (.md/.tex side) and `(file, decl)`",
    "(Lean side). Line numbers are convenience and re-derivable.",
    "",
    "**Guarantee boundary (read this).** The Lean column is machine-verified at the",
    "STATEMENT level: a sorry-free theorem/lemma certifies its *statement* is true.",
    "The `.tex` PROOFS are NOT Lean-verified at the proof level — they are human",
    "narratives refereed once at D0.5 and reconciled to the Lean *statements* by",
    "the proof-review loop. A `.tex` proof step can therefore be wrong while the (true) statement",
    "is Lean-certified; where the two disagree, the Lean proof is the ground truth.",
    "",
    "| obj_id | kind | Lean (file:decl) | .tex anchor | verdict | note |",
    "|---|---|---|---|---|---|",
  ];
  // Escape UNESCAPED pipes in EVERY interpolated cell (not just note): the tex
  // anchor is TeX prose, and an `E[Y|X]` or `\{x : |x| \le 1\}` in it added
  // columns and corrupted the banked table row.
  const mdCell = (s: string) => s.replace(/(?<!\\)\|/g, "\\|");
  for (const e of entries) {
    const lean = e.lean ? `${e.lean.file}:${e.lean.decl} (L${e.lean.line})` : "(none)";
    const tex = e.tex.label || e.tex.line_range || "(none)";
    lines.push(
      `| ${mdCell(e.obj_id)} | ${e.kind} | \`${mdCell(lean)}\` | ${mdCell(tex)} | ${e.verdict} | ${mdCell(e.note ?? "")} |`,
    );
  }
  return lines.join("\n") + "\n";
}

/** Persist the crosswalk: JSON backbone + the human-readable .md rendering. F5 writes it. */
export async function persistCrosswalk(
  jsonPath: string,
  mdPath: string,
  entries: CrosswalkEntry[],
): Promise<void> {
  await mkdir(path.dirname(jsonPath), { recursive: true });
  await writeFile(jsonPath, JSON.stringify(entries, null, 2) + "\n", "utf8");
  await writeFile(mdPath, renderCrosswalkMd(entries), "utf8");
}
