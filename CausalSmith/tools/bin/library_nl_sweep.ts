import { readFileSync } from "node:fs";
import { MODELS } from "../src/models.js";
import { resolve, join } from "node:path";
import { execSync } from "node:child_process";
import { loadLibrary, isTier1, declArea, type LibDecl } from "../src/library/schema.js";
import { runCodex } from "../src/shared/codex.js";
import { LEAN_ATTRS_PREFIX_SRC, LEAN_DECL_KEYWORDS, LEAN_MODIFIERS_PREFIX_SRC } from "../src/shared/lean_syntax.js";

/**
 * NL docstring sweep: dispatch codex (batched per source file, ≤ FILES_PER_CALL files
 * per call) to (a) write/normalize the first-paragraph NL translation of tier-1 decls
 * per the rubric prompt, and (b) add missing top-of-file module docstrings. Verifies
 * each batch by rebuilding the touched modules.
 *
 * Usage: npx tsx bin/library_nl_sweep.ts --area <Area> [--apply] [--all] [--module-docs-only]
 *          [--kinds def,structure] [--model mechanical|kernel] [--files-per-call N] [--limit N]
 *   default: dry-run (prints target counts per file)
 *   --apply: dispatch codex batches + lake build verification
 *   --all:   include decls that already have a docstring (normalization pass)
 *   --module-docs-only: skip decl docstrings entirely; only add missing top-of-file
 *     module docstrings (fast pass, larger batches)
 *   --kinds: restrict to these index kinds (default: every tier-1 decl). With a kind
 *     list, a decl whose first paragraph already carries crosslinks is skipped unless
 *     --all — the crosslink pass for definitions/structures ("re-annotation") is
 *     `--kinds def --model mechanical`.
 *   --model: codex tier (default kernel). --files-per-call: batch size (default 6).
 *   --limit: stop after N files (trial run).
 */

const args = process.argv.slice(2);
const areaIdx = args.indexOf("--area");
const area = areaIdx >= 0 ? args[areaIdx + 1] : null;
const apply = args.includes("--apply");
const all = args.includes("--all");
const moduleDocsOnly = args.includes("--module-docs-only");
// --no-verify: skip the per-batch lake build (comment-only edit passes; verify
// once at the end with a full build — useful when lake is contended).
const noVerify = args.includes("--no-verify");
const kindsIdx = args.indexOf("--kinds");
const kinds = kindsIdx >= 0 ? new Set(args[kindsIdx + 1].split(",").map((k) => k.trim()).filter(Boolean)) : null;
const modelIdx = args.indexOf("--model");
const modelTier = modelIdx >= 0 ? args[modelIdx + 1] : "kernel";
const fpcIdx = args.indexOf("--files-per-call");
const filesPerCall = fpcIdx >= 0 ? Number(args[fpcIdx + 1]) : 6;
const limitIdx = args.indexOf("--limit");
const fileLimit = limitIdx >= 0 ? Number(args[limitIdx + 1]) : Infinity;
if (!area) {
  console.error("usage: library_nl_sweep --area <Area> [--apply] [--all]");
  process.exit(1);
}

const root = resolve(import.meta.dirname, "..", "..", "..");
const lib = loadLibrary(root);

/** A file needs a module docstring if no `/-!` appears before its first declaration. */
function missingModuleDoc(file: string): boolean {
  let src: string;
  try {
    src = readFileSync(join(root, file), "utf8");
  } catch {
    return false;
  }
  const firstDecl = src.search(
    new RegExp(String.raw`^${LEAN_ATTRS_PREFIX_SRC}${LEAN_MODIFIERS_PREFIX_SRC}(?:${LEAN_DECL_KEYWORDS})\b`, "m"),
  );
  const head = firstDecl >= 0 ? src.slice(0, firstDecl) : src;
  return !head.includes("/-!");
}

/** Compiler-generated companions and instances have nothing to annotate. */
const isInstanceSource = (e: LibDecl) =>
  new RegExp(String.raw`^\s*${LEAN_ATTRS_PREFIX_SRC}${LEAN_MODIFIERS_PREFIX_SRC}instance\b`).test(
    (e.source ?? "").replace(/^\s*\/--[\s\S]*?-\/\s*/, ""),
  );
const firstParaAnnotated = (e: LibDecl) =>
  /\]\((?:hyp:|goal\)|step:)/.test((e.doc ?? "").trim().split(/\n\s*\n/)[0] ?? "");
const targets = moduleDocsOnly
  ? []
  : kinds
    ? lib.entries.filter(
        (e) =>
          declArea(e) === area &&
          kinds.has(e.kind) &&
          !!e.source &&
          // instances are skipped unless asked for by kind; compiler-derived
          // ones (`deriving …` is their whole source) have nothing to annotate
          (kinds.has("instance") ? !/^\s*deriving\b/.test((e.source ?? "").replace(/^\s*\/--[\s\S]*?-\/\s*/, "")) : !isInstanceSource(e)) &&
          (all || !firstParaAnnotated(e)),
      )
    : lib.entries.filter(
        (e) => declArea(e) === area && isTier1(e, lib.sidecars) && (all || !e.doc?.trim()),
      );
const byFile = new Map<string, LibDecl[]>();
for (const t of targets) byFile.set(t.file, [...(byFile.get(t.file) ?? []), t]);

// Files in this area lacking a module docstring (even with no decl targets).
const areaFiles = [...new Set(
  lib.entries.filter((e) => declArea(e) === area).map((e) => e.file),
)];
const noModDoc = new Set(areaFiles.filter(missingModuleDoc));
for (const f of noModDoc) if (!byFile.has(f)) byFile.set(f, []);

console.log(
  `${targets.length} target decls; ${noModDoc.size} files missing module docstring; ${byFile.size} files total (area ${area})`,
);
for (const [f, ds] of byFile) {
  const tags = [
    ds.length ? ds.map((d) => d.name.split(".").pop()).join(", ") : null,
    noModDoc.has(f) ? "+module-doc" : null,
  ].filter(Boolean);
  console.log(`  ${f}: ${tags.join(" ")}`);
}
if (!apply) process.exit(0);

const FILES_PER_CALL = moduleDocsOnly ? 15 : filesPerCall;
const promptTpl = readFileSync(
  resolve(import.meta.dirname, "..", "src", "library", "prompts", "nl_docstring.txt"),
  "utf8",
);
const files = [...byFile.keys()].slice(0, fileLimit);
for (let i = 0; i < files.length; i += FILES_PER_CALL) {
  const batch = files.slice(i, i + FILES_PER_CALL);
  const lines = batch.flatMap((f) =>
    byFile
      .get(f)!
      .map((d) => `${d.file} : ${d.line} : ${d.name} [${d.kind}] : ${d.statement.replace(/\s+/g, " ")}`),
  );
  const modDocLines = batch.filter((f) => noModDoc.has(f));
  const prompt = promptTpl
    .replace(
      "{{HEADER_CONTRACT}}",
      [
        "HEADER CONTRACT — Every generated Lean file begins, in order, with the optional copyright block, then `module`, contiguous imports written as `public import` (only a rare deliberate exception marked by a `-- private import` comment may use a private import), the `/-! ... -/` module docstring, and exactly one blanket section: `@[expose] public section` when the file defines a `def`, `abbrev`, `instance`, `structure`, `class`, or `inductive`, otherwise `public section`. Keep declarations bare: no per-declaration `public`, `private`, or `@[expose]`; helpers stay bare, and nothing is private unless it is truly file-local and never needed by a proof downstream. Run barrels and `Helpers.lean` are imports-only and use `public import` on every line.",
        "MODULE-SYSTEM CONSEQUENCES — A `module` file cannot import a legacy non-`module` file: every imported file must itself be a module file, and the scaffold must never add `import all`. A `def` whose body a downstream `rfl`, `decide`, or `unfold` needs must live in a file with `@[expose] public section`. A certificate evaluated by the kernel (`decide +kernel`) must not pass through well-founded recursion such as `Array.ofFn` or `termination_by`, because importers cannot see termination proofs; use a structural construction.",
      ].join("\n"),
    )
    .replace("{{targets}}", lines.length ? lines.join("\n") : "(none in this batch)")
    .replace("{{module_doc_files}}", modDocLines.length ? modDocLines.join("\n") : "(none in this batch)");
  console.log(
    `codex batch ${i / FILES_PER_CALL + 1}/${Math.ceil(files.length / FILES_PER_CALL)}: ${batch.join(", ")}`,
  );
  const out = await runCodex({
    prompt,
    cwd: root,
    model: modelTier === "mechanical" ? MODELS.codexMechanical : MODELS.codexKernel,
    reasoningEffort: "medium",
    leanLsp: false,
    webSearch: false,
    inactivityTimeoutMs: 40 * 60 * 1000,
  });
  if (out.stdout.trim()) console.log(out.stdout.trim());
  if (out.stderr.trim()) console.error(out.stderr.trim());
  if (!noVerify) {
    const modules = [...new Set(batch.map((f) => f.replace(/\//g, ".").replace(/\.lean$/, "")))];
    console.log(`verifying: lake build ${modules.join(" ")}`);
    execSync(`lake build ${modules.join(" ")}`, { cwd: root, stdio: "inherit", timeout: 2400_000 });
  }
}
console.log("sweep complete — rerun `lake exe library_index` to refresh the index");
