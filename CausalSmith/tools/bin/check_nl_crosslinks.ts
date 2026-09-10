import { readFileSync, readdirSync } from "node:fs";
import { join, resolve } from "node:path";
import {
  parseNlCrosslinks,
  crosslinkNames,
  crosslinkSteps,
  linksGoal,
  sourceBinders,
  sourceConstructorNames,
  sourceFieldNames,
} from "../src/shared/nl_crosslinks.js";
import {
  numberedClauses,
  structureDefinitionView,
  structureInductiveView,
  structureInstanceView,
  structureStatementView,
} from "../src/presentation/lean_structure.js";

/**
 * Lint for NL ↔ Lean crosslink annotations (`[phrase](hyp:name)` /
 * `[phrase](goal)` / `[phrase](step:N)` in docstring first paragraphs — see
 * src/shared/nl_crosslinks.ts for the convention).
 *
 * Usage: npx tsx bin/check_nl_crosslinks.ts [--root <causaleanRoot>] [--verbose]
 *
 * Always an ERROR (exit 1):
 *   - a crosslink references a binder name absent from the decl's signature
 *     (drift: hypothesis renamed after the docstring was annotated);
 *   - crosslink markup outside the first paragraph (the NL translation is the
 *     only sanctioned home);
 *   - an annotated theorem with incomplete coverage (a hyp-classified binder
 *     or the conclusion left unlinked);
 *   - an annotated definition with incomplete coverage (an explicit parameter
 *     or the defined object — `(goal)` — left unlinked);
 *   - a `(step:N)` naming a clause the statement does not have;
 *   - a HEADLINE theorem with no annotation at all (wave-2 policy: every
 *     headline theorem carries at minimum a `(goal)` link), unless its
 *     signature is unparseable (the site renders flat there).
 *
 * (--strict is retained as a no-op for old callers; the gate is always on.)
 */

const args = process.argv.slice(2);
const rootIdx = args.indexOf("--root");
const root =
  rootIdx >= 0 ? resolve(args[rootIdx + 1]) : resolve(import.meta.dirname, "..", "..", "..");
// --strict retained as a no-op: the coverage gate is always on since wave 2.
args.includes("--strict");
const verbose = args.includes("--verbose");

interface Entry {
  name: string;
  kind: string;
  file: string;
  line: number;
  doc?: string;
  source?: string;
  /** Elaborated binders (section variables included) — names a definition's
   *  crosslinks may target beyond the authored telescope. */
  params?: { n: string; t: string; bi: string }[];
  result?: string;
}
const idx = JSON.parse(readFileSync(join(root, "doc", "library_index.json"), "utf8")) as {
  entries: Entry[];
};

// Freshness guard: this lint validates annotations THROUGH the derived index.
// If the Lean sources carry substantially more crosslink markers than the
// index's docstrings, the index is stale (docstrings edited without
// `lake build && lake exe library_index`) and every check below would pass
// VACUOUSLY over pre-edit text (adversarial-audit finding F1, 2026-08-17).
{
  const { execFileSync } = await import("node:child_process");
  let srcCount = 0;
  try {
    const out = execFileSync(
      "grep",
      ["-rc", "--include=*.lean", "](hyp:", join(root, "Causalean")],
      { encoding: "utf8", maxBuffer: 64 * 1024 * 1024 },
    );
    for (const l of out.split("\n")) {
      const n = Number(l.slice(l.lastIndexOf(":") + 1));
      if (Number.isFinite(n)) srcCount += n;
    }
  } catch (err) {
    // grep exits 1 when NO file matches — that is a real count of 0.
    const e = err as { status?: number; stdout?: string };
    if (e.status !== 1) throw err;
  }
  let idxCount = 0;
  for (const e of idx.entries) {
    if (e.name.startsWith("Causalean.") && e.doc) {
      idxCount += (e.doc.match(/\]\(hyp:/g) ?? []).length;
    }
  }
  // Line-based grep counts markers once per line; multi-marker lines make the
  // source count an undercount, so only a SOURCE ≫ INDEX gap signals staleness.
  if (srcCount > idxCount * 1.1 + 50) {
    console.error(
      `STALE INDEX: Causalean sources carry ~${srcCount} \`](hyp:\` marker lines but the ` +
        `index's docstrings only ${idxCount}. Regenerate before linting: ` +
        `lake build && lake exe library_index (then npm run embed:library).`,
    );
    process.exit(1);
  }
}

const headline = new Set<string>();
try {
  for (const f of readdirSync(join(root, "doc", "library_review"))) {
    if (!f.endsWith(".json")) continue;
    const d = JSON.parse(readFileSync(join(root, "doc", "library_review", f), "utf8"));
    for (const n of d.headline_theorems ?? []) headline.add(n);
  }
} catch {
  /* no sidecars: coverage gate simply has no headline set */
}

const errors: string[] = [];
const incomplete: string[] = [];
const unannotatedHeadline: string[] = [];
let annotated = 0;
let fullyCovered = 0;
let defsAnnotated = 0;
let defsCovered = 0;
let defsUnannotated = 0;

/** Number of top-level clauses `(step:N)` may address, or null when the
 *  statement does not structure (then any step link is unverifiable, not wrong). */
function clauseCount(e: Entry): number | null {
  if (!e.source) return null;
  const view =
    e.kind === "def"
      ? structureDefinitionView(e.source, e.result ?? "")
      : e.kind === "instance"
        ? structureInstanceView(e.source, e.name.split(".").pop())
        : e.kind === "inductive"
          ? structureInductiveView(e.source, e.result ?? "")
          : e.kind === "theorem"
            ? structureStatementView(e.source)
            : null;
  return view && view.conclusions.length > 0 ? numberedClauses(view.conclusions).length : view ? 0 : null;
}

// Theorems and definitions get the full treatment (name validation +
// coverage: a theorem's hyp-classified binders and its conclusion; a
// definition's explicit parameters and its defined object, `(goal)`);
// structures/classes get name validation only — a structure's crosslinks may
// target its parameter binders or its `where`-block fields, and it has no
// conclusion, so `(goal)` there is an error.
const KINDS = new Set(["theorem", "structure", "class", "def", "instance", "inductive"]);
const decls = idx.entries.filter((e) => KINDS.has(e.kind) && e.name.startsWith("Causalean."));
const theorems = decls.filter((e) => e.kind === "theorem");

for (const e of decls) {
  const doc = e.doc ?? "";
  const paras = doc.trim().split(/\n\s*\n/);
  // Whitespace-collapsed, matching the site's nlOf: a crosslink marker wrapped
  // across a source line must parse the same here as on the rendered page.
  const firstPara = (paras[0] ?? "").replace(/\s+/g, " ");
  const rest = paras.slice(1).join("\n\n");
  const restLinks = parseNlCrosslinks(rest).filter((s) => s.links);
  if (restLinks.length > 0) {
    errors.push(`${e.name} (${e.file}:${e.line}): crosslink markup outside the first paragraph`);
  }
  const names = crosslinkNames(firstPara);
  const hasGoal = linksGoal(firstPara);
  const steps = crosslinkSteps(firstPara);
  if (names.length === 0 && !hasGoal && steps.length === 0) {
    if (e.kind === "def") defsUnannotated++;
    // An unannotated HEADLINE theorem is a hard defect (every headline theorem
    // carries at least a `(goal)` link since wave 2) — unless its signature is
    // unparseable, where the site renders flat and annotations would be inert.
    if (e.kind === "theorem" && headline.has(e.name) && e.source && sourceBinders(e.source)) {
      unannotatedHeadline.push(`${e.name} (${e.file}:${e.line})`);
    }
    continue;
  }
  annotated++;
  const clauseBearing = e.kind === "theorem" || e.kind === "def" || e.kind === "instance" || e.kind === "inductive";
  if ((hasGoal || steps.length > 0) && !clauseBearing) {
    errors.push(`${e.name} (${e.file}:${e.line}): (goal)/(step:N) crosslink on a ${e.kind} — no conclusion to link`);
  }
  if (steps.length > 0) {
    const n = clauseCount(e);
    const bad = n === null ? [] : steps.filter((k) => k < 1 || k > n);
    if (bad.length > 0) {
      errors.push(`${e.name} (${e.file}:${e.line}): (step:${bad.join("/")}) but the statement has ${n} clause(s)`);
    }
  }
  const binders = e.source ? sourceBinders(e.source) : null;
  if (!binders) {
    // Unparseable signature: can't validate names — surface loudly in verbose,
    // but don't fail; the site falls back to unstructured rendering there too.
    if (verbose) console.log(`  (unparsed signature, names unchecked) ${e.name}`);
    continue;
  }
  const declared = new Set(binders.flatMap((b) => b.names));
  if (e.kind === "structure" || e.kind === "class") {
    for (const f of sourceFieldNames(e.source ?? "")) declared.add(f);
  }
  // A `variable`-introduced section parameter is absent from the authored
  // source but shown as a parameter row; the elaborated binder list names it.
  for (const p of e.params ?? []) if (p.n) declared.add(p.n);
  // An inductive's constructors are rows too (`[phrase](hyp:ctorName)`).
  if (e.kind === "inductive") for (const c of sourceConstructorNames(e.source ?? "")) declared.add(c);
  const unknown = names.filter((n) => !declared.has(n));
  // A source the index truncated at sourceSliceCap hides late binders/fields —
  // names past the cut cannot be validated (they render as inert spans on the
  // site, which is harmless), so skip the unknown-name check there.
  if (unknown.length > 0 && !(e.source ?? "").includes("… truncated")) {
    errors.push(
      `${e.name} (${e.file}:${e.line}): crosslink names not in signature: ${unknown.join(", ")}`,
    );
  }
  const linked = new Set(names);
  if (e.kind === "def" || e.kind === "instance" || e.kind === "inductive") {
    defsAnnotated++;
    const uncovered = binders.filter((b) => b.isExplicit && !b.names.some((n) => linked.has(n)));
    if (uncovered.length === 0 && hasGoal) {
      defsCovered++;
    } else {
      const what = [...uncovered.map((b) => b.names.join(" ")), ...(hasGoal ? [] : ["(goal)"])];
      incomplete.push(`${e.name}: unlinked ${what.join(", ")}`);
    }
    continue;
  }
  if (e.kind !== "theorem") continue; // structures: name validation only
  const uncoveredHyps = binders.filter((b) => b.isHyp && !b.names.some((n) => linked.has(n)));
  if (uncoveredHyps.length === 0 && hasGoal) {
    fullyCovered++;
  } else {
    const what = [
      ...uncoveredHyps.map((b) => b.names.join(" ")),
      ...(hasGoal ? [] : ["(goal)"]),
    ];
    incomplete.push(`${e.name}: unlinked ${what.join(", ")}`);
  }
}

console.log(
  `nl-crosslinks: ${decls.length} Causalean decls (${theorems.length} theorems) · ` +
    `${annotated} annotated · ${fullyCovered} theorems fully covered · ` +
    `${defsCovered}/${defsAnnotated} annotated definitions fully covered (${defsUnannotated} definitions unannotated) · ` +
    `${incomplete.length} incomplete · ` +
    `${unannotatedHeadline.length}/${headline.size} headline theorems unannotated`,
);
if (verbose && incomplete.length > 0) {
  console.log(`\nIncomplete coverage:\n  ${incomplete.join("\n  ")}`);
}
// Since wave 2 (2026-08-17) both are hard defects by default, not just under
// --strict: an annotated theorem (or definition) must be FULLY covered, and
// every headline theorem must be annotated (at minimum a `(goal)` link on the
// conclusion).
if (incomplete.length > 0) {
  errors.push(...incomplete.map((s) => `incomplete coverage: ${s}`));
}
if (unannotatedHeadline.length > 0) {
  errors.push(...unannotatedHeadline.map((s) => `headline theorem unannotated: ${s}`));
}
if (errors.length > 0) {
  console.error(`\nERRORS (${errors.length}):\n  ${errors.join("\n  ")}`);
  process.exit(1);
}
