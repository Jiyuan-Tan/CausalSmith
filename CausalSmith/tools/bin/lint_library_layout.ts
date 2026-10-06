#!/usr/bin/env -S npx tsx
/** Structural Causalean layout checks. This deliberately reads text, not oleans. */
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";
import { maskLeanCommentsAndStrings } from "../src/shared/lean_mask.js";
import { parseLeanImport } from "../src/shared/lean_syntax.js";
import {
  FALLBACK_MATHLIB_TOP_LEVEL, LAYER_PREFIXES, MATHLIB_DIR_EXCEPTIONS,
  NAMESPACE_ALLOWLIST, SEEDED_RUN_BASENAMES, SEEDED_RUN_SLUGS,
} from "../src/library/layout_rules.js";

export interface Finding { rule: string; path: string; line?: number; message: string; severity?: "error" | "warning" }
interface Baseline { version?: number; violations?: Finding[] }
const TOOLS_ROOT = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");
const DEFAULT_ROOT = path.resolve(TOOLS_ROOT, "..", "..");
const DEFAULT_BASELINE = path.join(TOOLS_ROOT, "lint", "layout_baseline.json");

function walk(dir: string, predicate: (full: string, name: string, isDirectory: boolean) => void): void {
  if (!existsSync(dir)) return;
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    predicate(full, entry.name, entry.isDirectory());
    if (entry.isDirectory() && entry.name !== "tmp") walk(full, predicate);
  }
}

function normalizeName(name: string): string {
  return name.replace(/\.lean$/i, "")
    .replace(/([a-z0-9])([A-Z])/g, "$1-$2").replace(/([A-Z]+)([A-Z][a-z])/g, "$1-$2")
    .replace(/[^A-Za-z0-9]+/g, "-").replace(/([a-zA-Z])(\d)/g, "$1-$2")
    .replace(/(\d)([a-zA-Z])/g, "$1-$2").replace(/^-|-$/g, "").toLowerCase();
}

function relative(root: string, full: string): string { return path.relative(root, full).replaceAll(path.sep, "/"); }
function moduleForFile(file: string): string { return file.replace(/\.lean$/, "").replaceAll("/", "."); }

function layerFromPrefixes(module: string): number | undefined {
  if (!module.startsWith("Causalean.")) return undefined;
  const tail = module.slice("Causalean.".length).replaceAll(".", "/");
  for (const [prefix, layer] of LAYER_PREFIXES) if (tail === prefix || tail.startsWith(`${prefix}/`)) return layer;
  return undefined;
}

function importsOnly(source: string): boolean {
  let imports = 0;
  for (const line of maskLeanCommentsAndStrings(source).split(/\r?\n/)) {
    if (!line.trim() || line.trim() === "module") continue;
    if (parseLeanImport(line)) { imports++; continue; }
    // A blanket public section is harmless in an imports-only barrel (modulize emits one).
    if (/^[ \t]*(?:@\[[^\]]*\][ \t]*)*public\s+(?:noncomputable\s+)?section\s*$/.test(line)) continue;
    return false;
  }
  return imports > 0;
}

function barrelLayer(module: string): number | undefined {
  const tail = module.slice("Causalean.".length).replaceAll(".", "/");
  const layers = [layerFromPrefixes(module)];
  for (const [prefix, layer] of LAYER_PREFIXES)
    if (prefix === tail || prefix.startsWith(`${tail}/`)) layers.push(layer);
  const known = layers.filter((layer): layer is number => layer !== undefined);
  return known.length ? Math.max(...known) : undefined;
}

function firstNamespace(source: string): { name: string; line: number } | null {
  const lines = maskLeanCommentsAndStrings(source).split(/\r?\n/);
  for (const [i, line] of lines.entries()) {
    const m = /^\s*namespace\s+([\p{L}\p{N}_'.«»!?]+)/u.exec(line);
    if (!m) continue;
    if (m[1] !== "Causalean") return { name: m[1], line: i + 1 };
    // Most legacy files open `namespace Causalean` and immediately open their
    // area beneath it. Treat that pair as the first effective namespace.
    for (let j = i + 1; j < lines.length; j++) {
      const child = /^\s*namespace\s+([\p{L}\p{N}_'.«»!?]+)/u.exec(lines[j] ?? "");
      if (!child) continue;
      return { name: child[1].includes(".") ? child[1] : `Causalean.${child[1]}`, line: j + 1 };
    }
    return { name: m[1], line: i + 1 };
  }
  return null;
}

function qidNames(root: string): Set<string> {
  const names = new Set<string>();
  const study = path.join(root, "CausalSmith", "doc", "study");
  if (existsSync(study)) for (const entry of readdirSync(study, { withFileTypes: true })) if (entry.isDirectory()) names.add(normalizeName(entry.name));
  const research = path.join(root, "CausalSmith", "doc", "research");
  walk(research, (full, name, directory) => {
    if (!directory) return;
    if (existsSync(path.join(full, "state.json")) || existsSync(path.join(full, `${name}_state.json`)))
      names.add(normalizeName(name.replace(/_v\d+$/, "")));
  });
  return names;
}

function mathlibTopLevel(root: string): Set<string> {
  const dir = path.join(root, ".lake", "packages", "mathlib", "Mathlib");
  const actual = existsSync(dir) ? readdirSync(dir, { withFileTypes: true }).filter((e) => e.isDirectory()).map((e) => e.name) : FALLBACK_MATHLIB_TOP_LEVEL;
  return new Set([...actual, ...MATHLIB_DIR_EXCEPTIONS]);
}

// SIZE findings are keyed without their message: the message carries the line count, and an
// already-baselined oversized file must not resurface every time its length changes by a few lines.
// Keys never include the line: a header edit shifts every line in a file and must not resurface
// baselined findings. SIZE also drops its message (which carries the line count). The SEVERITY is
// part of the key: a grandfathered 600–900 warning must not suppress a later >900 hard-cap error.
export function baselineKey(f: Finding): string {
  const message = f.rule === "SIZE" ? "" : f.message;
  return `${f.rule}\u0000${f.path.replaceAll("\\", "/")}\u0000${message}\u0000${f.severity ?? "error"}`;
}

/** Findings that fail a gate. Advisory findings (the 600–900 soft cap, whose >900 hard cap is a
 * separate error) are reported but never block, matching `lint_module_headers`'s CLI and the
 * project rule "normally ≤600 lines; split before ~900". Every consumer — this CLI and the study
 * promotion gate — shares this predicate so the two can never drift apart. */
export function isBlockingFinding(f: { severity?: "error" | "warning" }): boolean {
  return (f.severity ?? "error") !== "warning";
}
function loadBaseline(file: string | undefined): Set<string> {
  if (!file) return new Set();
  const parsed = JSON.parse(readFileSync(file, "utf8")) as Baseline | Finding[];
  const findings = Array.isArray(parsed) ? parsed : parsed.violations ?? [];
  return new Set(findings.map(baselineKey));
}

/** Runs all checks. `root` is injectable so unit tests can use a small synthetic repository. */
export function lintLibraryLayout(root: string): Finding[] {
  const causalean = path.join(root, "Causalean");
  const files: string[] = [], names = new Set([
    ...SEEDED_RUN_SLUGS.map(normalizeName), ...SEEDED_RUN_BASENAMES.map(normalizeName), ...qidNames(root),
  ]);
  const findings: Finding[] = [];
  const add = (rule: string, full: string, message: string, line?: number, severity: "error" | "warning" = "error") =>
    findings.push({ rule, path: relative(root, full), line, message, severity });
  walk(causalean, (full, name, directory) => {
    if (directory || !name.endsWith(".lean")) {
      if ((directory || name.endsWith(".lean")) && names.has(normalizeName(name)))
        add("RUN-NAME", full, `name matches research/study run slug ${normalizeName(name)}`);
      return;
    }
    files.push(full);
  });
  const topLevel = mathlibTopLevel(root);
  const barrelLayers = new Map<string, number>();
  const shimModules = new Set<string>();
  for (const file of files) {
    const rel = relative(root, file), module = moduleForFile(rel), source = readFileSync(file, "utf8");
    if (source.includes("deprecated_module")) shimModules.add(module);
    if (existsSync(file.replace(/\.lean$/, "")) && importsOnly(source)) {
      const layer = barrelLayer(module);
      if (layer !== undefined) barrelLayers.set(module, layer);
    }
  }
  const layerOf = (module: string): number | undefined => barrelLayers.get(module) ?? layerFromPrefixes(module);
  for (const file of files.sort()) {
    const source = readFileSync(file, "utf8"), lines = source.split(/\r?\n/);
    const maskedLines = maskLeanCommentsAndStrings(source).split(/\r?\n/), rel = relative(root, file);
    const module = moduleForFile(rel);
    const layerExempt = source.includes("deprecated_module");
    for (const [i, line] of maskedLines.entries()) {
      const imp = parseLeanImport(line);
      if (!imp) continue;
      if (imp.module.startsWith("CausalSmith")) add("NO-CAUSALSMITH", file, `Causalean must not import ${imp.module}`, i + 1);
      if (imp.module.startsWith("Causalean.") && !layerExempt && !shimModules.has(imp.module)) {
        const from = layerOf(module), to = layerOf(imp.module);
        if (from === undefined || to === undefined)
          add("LAYER", file, `unknown layer for ${from === undefined ? module : imp.module}`, i + 1);
        else if (to > from)
          add("LAYER", file, `${module} (L${from}) imports higher layer ${imp.module} (L${to})`, i + 1);
      }
      if (rel.startsWith("Causalean/Mathlib/") && imp.module.startsWith("Causalean.") &&
          !imp.module.startsWith("Causalean.Mathlib.") && !imp.module.startsWith("Causalean.Tactic."))
        add("MATHLIB-PURITY", file, `Mathlib file imports forbidden project module ${imp.module}`, i + 1);
    }
    if (rel.startsWith("Causalean/Mathlib/") && rel.split("/").length > 3) {
      const first = rel.split("/")[2];
      if (!topLevel.has(first)) add("MATHLIB-PURITY", file, `Mathlib top-level directory ${first} is not mirrored from Mathlib`);
    }
    const lineCount = lines.length;
    if (lineCount > 900) add("SIZE", file, `${lineCount} lines exceeds hard cap of 900`);
    else if (lineCount > 600) add("SIZE", file, `${lineCount} lines exceeds normal cap of 600`, undefined, "warning");
    const ns = firstNamespace(source);
    if (ns && !NAMESPACE_ALLOWLIST.some((prefix) => ns.name === prefix || ns.name.startsWith(`${prefix}.`))) {
      const top = rel.split("/")[1];
      const expected = `Causalean.${top}`;
      if (!(ns.name === expected || ns.name.startsWith(`${expected}.`)))
        add("NAMESPACE", file, `first namespace ${ns.name} must start with ${expected}`, ns.line);
    }
  }
  // `Mathlib/` itself needs a separate loose-file check; keep it here to avoid treating the root barrel as one.
  const mathlibDir = path.join(causalean, "Mathlib");
  if (existsSync(mathlibDir)) for (const entry of readdirSync(mathlibDir, { withFileTypes: true }))
    if (entry.isFile() && entry.name.endsWith(".lean")) add("MATHLIB-PURITY", path.join(mathlibDir, entry.name), "Mathlib must not contain top-level .lean files");

  const indexFile = path.join(root, "doc", "library_index.json");
  if (existsSync(indexFile)) {
    const index = JSON.parse(readFileSync(indexFile, "utf8")) as { entries?: { module?: string; file?: string }[] };
    const headlines = new Set<string>();
    const reviews = path.join(root, "doc", "library_review");
    if (existsSync(reviews)) for (const entry of readdirSync(reviews)) if (entry.endsWith(".json")) {
      const sidecar = JSON.parse(readFileSync(path.join(reviews, entry), "utf8")) as { headline_theorems?: string[] };
      for (const name of sidecar.headline_theorems ?? []) headlines.add(name);
    }
    const byFile = new Map<string, number>();
    for (const decl of index.entries ?? []) {
      // Decision (c), 2026-09-13: the headline policy is 1–N per file everywhere, `Mathlib/` included
      // (cap raised 3 → 5 on 2026-09-18: several consolidated files carry more than three genuine
      //  flagship results, and failing a promotion on another file's count deadlocked the gate)
      // (the earlier "0 in Mathlib/" recommendation was overruled), so only the cap below is enforced.
      if (headlines.has((decl as { name?: string }).name ?? "") && decl.file)
        byFile.set(decl.file, (byFile.get(decl.file) ?? 0) + 1);
    }
    for (const [file, count] of byFile) if (count > 5) add("HEADLINES", path.join(root, file), `${count} headline entries exceeds cap of 5`);
  }
  return findings.sort((a, b) => `${a.rule}:${a.path}:${a.line ?? 0}`.localeCompare(`${b.rule}:${b.path}:${b.line ?? 0}`));
}

function main(): void {
  const args = process.argv.slice(2), json = args.includes("--json");
  const value = (flag: string): string | undefined => {
    const i = args.indexOf(flag), candidate = i < 0 ? undefined : args[i + 1];
    return candidate && !candidate.startsWith("--") ? candidate : undefined;
  };
  const root = path.resolve(value("--root") ?? DEFAULT_ROOT);
  const all = lintLibraryLayout(root);
  const baselineFile = path.resolve(value("--baseline") ?? DEFAULT_BASELINE);
  if (args.includes("--write-baseline")) {
    const output = path.resolve(value("--write-baseline") ?? baselineFile);
    mkdirSync(path.dirname(output), { recursive: true });
    writeFileSync(output, `${JSON.stringify({ version: 1, violations: all }, null, 2)}\n`);
  }
  const baseline = loadBaseline(baselineFile);
  const findings = all.filter((f) => !baseline.has(baselineKey(f)));
  const blocking = findings.filter(isBlockingFinding);
  if (json) console.log(JSON.stringify({ findings, blocking, total: all.length, suppressed: all.length - findings.length }, null, 2));
  else for (const f of findings) console.log(`${isBlockingFinding(f) ? f.rule : `${f.rule} (advisory)`}: ${f.path}${f.line ? `:${f.line}` : ""}: ${f.message}`);
  if (blocking.length) process.exitCode = 1;
}
if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
