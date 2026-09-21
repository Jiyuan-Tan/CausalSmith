#!/usr/bin/env -S npx tsx
/** Check the module-system source header contract without requiring Lean. */
import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";
import { maskLeanCommentsAndStrings } from "../src/shared/lean_mask.js";
import { LEAN_DECL_HEADER_RE, isLeanModuleFile, parseLeanImport } from "../src/shared/lean_syntax.js";

export interface Finding { path: string; line: number; rule: string; message: string; severity: "error" | "warning" }
const TOOLS_ROOT = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");
const REPO_ROOT = path.resolve(TOOLS_ROOT, "..", "..");
const DEF_LIKE = new Set(["def", "abbrev", "instance", "structure", "class", "inductive"]);

function filesUnder(target: string): string[] {
  if (!existsSync(target)) return [];
  if (statSync(target).isFile()) return target.endsWith(".lean") ? [target] : [];
  const out: string[] = [];
  const walk = (dir: string) => {
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
      const full = path.join(dir, entry.name);
      // `.lake` holds downloaded dependencies (Mathlib, proofwidgets, …) and build output, not
      // our source; linting it reported thousands of module-contract errors against code we do
      // not own. `node_modules` is excluded for the same reason.
      if (entry.isDirectory()) { if (!["tmp", ".lake", "node_modules"].includes(entry.name)) walk(full); }
      else if (entry.isFile() && entry.name.endsWith(".lean")) out.push(full);
    }
  };
  walk(target);
  return out;
}

/** End offset of the header `/-! -/` docstring: the first one, and only when it opens before the
 * first declaration — a `/-!` section comment further down the file is not a header anchor. */
function headerModuleDocEnd(source: string, firstDeclOffset: number | null): number | null {
  const start = source.indexOf("/-!");
  if (start < 0 || (firstDeclOffset !== null && start > firstDeclOffset)) return null;
  const end = source.indexOf("-/", start + 3);
  return end < 0 ? null : end + 2;
}

function display(file: string): string { return path.relative(REPO_ROOT, file).replaceAll(path.sep, "/") || file; }

export function lintModuleHeaders(files: string[], allowLegacy = true): { findings: Finding[]; legacyCount: number } {
  const findings: Finding[] = [];
  const add = (file: string, line: number, rule: string, message: string, severity: "error" | "warning" = "error") =>
    findings.push({ path: display(file), line, rule, message, severity });
  let legacyCount = 0;
  for (const file of files.sort()) {
    const source = readFileSync(file, "utf8");
    if (!isLeanModuleFile(source)) {
      legacyCount++;
      if (!allowLegacy) add(file, 1, "missing-module-header", "first non-comment line must be `module`");
      continue;
    }
    const lines = source.split(/\r?\n/);
    const masked = maskLeanCommentsAndStrings(source);
    const maskedLines = masked.split(/\r?\n/);
    maskedLines.forEach((line, i) => {
      const imp = parseLeanImport(line);
      if (imp && !imp.isPublic && !/--\s*private import\b/.test(lines[i - 1] ?? ""))
        add(file, i + 1, "non-public-import", "imports must use `public import` unless preceded by `-- private import`");
    });
    const sectionLines = maskedLines.flatMap((line, i) =>
      /^[ \t]*(?:@\[[^\]]*\][ \t]*)*public\s+(?:noncomputable\s+)?section\b/.test(line) ? [i] : []);
    const declarationLines = maskedLines.flatMap((line, i) => LEAN_DECL_HEADER_RE.test(line) ? [i] : []);
    if (declarationLines.length > 0 && sectionLines.length !== 1) {
      add(file, 1, "blanket-public-section", `expected exactly one blanket public section, found ${sectionLines.length}`);
      continue;
    }
    if (declarationLines.length === 0 && sectionLines.length === 0) continue;
    if (sectionLines.length !== 1) {
      add(file, 1, "blanket-public-section", `expected at most one blanket public section in a declaration-free file, found ${sectionLines.length}`);
      continue;
    }
    const section = sectionLines[0];
    const importLines = maskedLines.flatMap((line, i) => parseLeanImport(line) ? [i] : []);
    const firstDeclOffset = declarationLines.length > 0
      ? lines.slice(0, declarationLines[0]).join("\n").length : null;
    const docEnd = headerModuleDocEnd(source, firstDeclOffset);
    const sectionOffset = lines.slice(0, section + 1).join("\n").length;
    // A file without a `/-! -/` docstring (vendored packages) only needs the section after its imports.
    if ((importLines.length > 0 && section <= Math.max(...importLines)) || (docEnd !== null && sectionOffset < docEnd))
      add(file, section + 1, "blanket-public-section-position", "blanket public section must follow imports and the first `/-!` docstring");
    // `@[expose]` controls whether a definition's BODY is exported, so a section only needs it
    // for a definition that is actually exported and not already exposed on its own. Two cases
    // must therefore be excluded, or the rule fires on files it cannot help:
    //   * `private` definitions are never exported, so there is no body to expose;
    //   * a definition carrying its own `@[expose]` attribute is already exposed per-declaration,
    //     which is as valid as exposing the whole section.
    const defLike = maskedLines.some((line) => {
      const m = LEAN_DECL_HEADER_RE.exec(line);
      if (m === null || !DEF_LIKE.has(m[1])) return false;
      const head = line.slice(0, m.index + m[0].length);
      if (/(?:^|\s)private\s/.test(head)) return false;
      return !/@\[\s*[^\]]*\bexpose\b[^\]]*\]/.test(head);
    });
    const exposed = /@\[\s*expose\s*\]/.test(maskedLines[section]);
    if (defLike && !exposed)
      add(file, section + 1, "expose-section", "def-like files require `@[expose] public section`");
    else if (!defLike && exposed)
      add(file, section + 1, "expose-section", "`@[expose]` is harmless but has no effect in a theorem-only file", "warning");
  }
  return { findings, legacyCount };
}

function main(): void {
  const args = process.argv.slice(2), json = args.includes("--json");
  const allowLegacy = args.includes("--allow-legacy") || !args.includes("--strict");
  const pathsAt = args.indexOf("--paths");
  // `third_party/` is vendored upstream Lean (lean-rademacher, optlib), adapted only enough to
  // build against our toolchain pin. It is not ours to restyle, and re-syncing upstream would
  // undo any edits, so the module-header contract does not apply to it. Including it accounted
  // for 1388 of 1425 reported errors and buried the ~37 real ones in our own source.
  const inputs = pathsAt < 0
    ? [path.join(REPO_ROOT, "Causalean"), path.join(REPO_ROOT, "Causalean.lean"), path.join(REPO_ROOT, "CausalSmith", "CausalSmith"), path.join(REPO_ROOT, "CausalSmith", "CausalSmith.lean")]
    : args.slice(pathsAt + 1).filter((x) => !x.startsWith("--"));
  const files = inputs.flatMap((p) => filesUnder(path.resolve(process.cwd(), p)));
  const result = lintModuleHeaders([...new Set(files)], allowLegacy);
  if (json) console.log(JSON.stringify(result, null, 2));
  else {
    for (const f of result.findings) console.log(`${f.path}:${f.line}: ${f.rule}: ${f.message}`);
    if (allowLegacy) console.log(`legacy-module-files: ${result.legacyCount}`);
  }
  if (result.findings.some((finding) => finding.severity === "error")) process.exitCode = 1;
}
if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
