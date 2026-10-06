#!/usr/bin/env -S npx tsx
/**
 * Re-stamp shipped paper bundles: recompile page 1 with the current identity values, change
 * nothing else.
 *
 * In plain words: a paper's number, version, area, revised date and — once it is deposited —
 * its DOI are printed in the left margin of page 1. Those values can change after the PDF was
 * built (a DOI is only minted at deposit time), and the only ways to get them onto the page used
 * to be a multi-hour P4 re-emit or a hand edit of a derived file. This does the small thing
 * instead: refresh the template macros, regenerate `paper_stamp.tex`, run `latexmk`, and prove
 * the result is the same document before replacing anything.
 *
 * DRY RUN IS THE DEFAULT. Without `--write` it compiles, verifies and prints the table, and the
 * shipped bundles are not touched. The exit status is non-zero if any bundle failed.
 *
 * Usage:
 *   restamp_paper.ts <bundleDir>... [--write]
 *   restamp_paper.ts --all <presentationRoot> [--write]
 *
 * See `src/presentation/restamp.ts` for what may be written and why the version cannot move.
 */
import process from "node:process";
import { readdir, readFile } from "node:fs/promises";
import { join, resolve } from "node:path";
import { paperSeriesPrefix } from "../src/local_config.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import {
  RESTAMP_TABLE_HEADER, formatRestampRow, restampBundle, type RestampResult,
} from "../src/presentation/restamp.js";
import { isBundleEmitBusy } from "../src/presentation/emit_lock.js";

/** Every directory under `root` that holds a `meta.json`. `doc/presentation/` also carries
 *  non-bundle entries (`_wp_registry.json`), so the bundle contract — not the name — is the test. */
async function listBundles(root: string): Promise<string[]> {
  const entries = await readdir(root, { withFileTypes: true });
  const dirs: string[] = [];
  for (const entry of entries) {
    if (!entry.isDirectory()) continue;
    const ok = await readFile(join(root, entry.name, "meta.json"), "utf8").then(() => true, () => false);
    if (ok) dirs.push(join(root, entry.name));
  }
  return dirs.sort();
}

function usage(): string {
  return [
    "Usage: restamp_paper.ts <bundleDir>... [--write]",
    "       restamp_paper.ts --all <presentationRoot> [--write]",
    "",
    "  --write   apply the verified result (default: dry run, nothing is written)",
    "  --all <d> restamp every bundle under <d> (a directory of bundle directories)",
  ].join("\n");
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2);
  if (argv.length === 0 || argv.includes("--help") || argv.includes("-h")) {
    console.log(usage());
    return;
  }
  const write = argv.includes("--write");
  const targets: string[] = [];
  let all: string | null = null;
  for (let i = 0; i < argv.length; i += 1) {
    const tok = argv[i]!;
    if (tok === "--write") continue;
    if (tok === "--all") {
      const value = argv[i + 1];
      if (value === undefined || value.startsWith("--")) throw new Error("--all requires a directory.");
      all = resolve(value);
      i += 1;
      continue;
    }
    if (tok.startsWith("--")) throw new Error(`Unknown flag '${tok}'.\n\n${usage()}`);
    targets.push(resolve(tok));
  }
  if (all !== null) targets.push(...(await listBundles(all)));
  if (targets.length === 0) throw new Error(`No bundle directories given.\n\n${usage()}`);

  // Resolved ONCE for the whole run, before the first bundle: one operation carries one series,
  // so no later environment change can make the number stamped and the registry it is checked
  // against disagree. Same rule (and same function) as P4 and the backfill.
  const seriesPrefix = paperSeriesPrefix();
  const repoRoot = findCausalSmithRoot(all ?? targets[0]!);

  console.error(
    `restamp: ${targets.length} bundle(s), repo ${repoRoot}, series ${seriesPrefix}` +
      `${write ? "" : " [DRY RUN — nothing will be written]"}`,
  );

  // Sequential on purpose: each bundle runs a full LaTeX compile (~a minute), and a dozen at once
  // would fight over the same CPUs and the same TeX Live on a network filesystem for no gain.
  const results: RestampResult[] = [];
  for (const dir of targets) {
    let result: RestampResult;
    try {
      result = await restampBundle(dir, { repoRoot, seriesPrefix, write });
    } catch (err) {
      const message = isBundleEmitBusy(err)
        ? "an emit of this bundle is in progress; nothing was read or written"
        : err instanceof Error ? err.message : String(err);
      result = {
        bundleDir: dir, bundleId: dir.split(/[/\\]/).filter(Boolean).pop() ?? dir,
        wpNumber: null, version: null, revised: null, doi: null, pages: null,
        verdict: "blocked", ok: false, written: [], detail: message,
      };
    }
    results.push(result);
    console.error(`  · ${result.bundleId}: ${result.verdict}`);
  }

  const width = Math.max(RESTAMP_TABLE_HEADER[0].length, ...results.map((r) => r.bundleId.length));
  const pad = (s: string, w: number) => (s.length >= w ? s : s + " ".repeat(w - s.length));
  console.log("");
  console.log([
    pad(RESTAMP_TABLE_HEADER[0], width), pad(RESTAMP_TABLE_HEADER[1], 13),
    pad(RESTAMP_TABLE_HEADER[2], 4), pad(RESTAMP_TABLE_HEADER[3], 10),
    pad(RESTAMP_TABLE_HEADER[4], 22), pad(RESTAMP_TABLE_HEADER[5], 5),
    RESTAMP_TABLE_HEADER[6],
  ].join("  "));
  for (const r of results) console.log(formatRestampRow(r, width));

  const failed = results.filter((r) => !r.ok);
  console.log("");
  console.log(
    `${results.length} bundle(s): ${results.filter((r) => r.verdict === "written").length} written, ` +
      `${results.filter((r) => r.verdict === "would-write").length} would write, ` +
      `${results.filter((r) => r.verdict === "unchanged").length} unchanged, ${failed.length} failed.`,
  );
  console.log(write ? "" : "DRY RUN — nothing written. Re-run with --write to apply.");
  if (failed.length > 0) {
    console.error(`\n${failed.length} bundle(s) failed:`);
    for (const r of failed) console.error(`\n--- ${r.bundleId} (${r.verdict}) ---\n${r.detail}`);
    process.exitCode = 1;
  }
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exitCode = 1;
});
