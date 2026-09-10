#!/usr/bin/env node
/**
 * Rename a presentation bundle's `proofs/<obj_id>.tex` files to the portable spelling
 * (`proof_files.ts`: `thm:x.tex` → `thm--x.tex`). A bundle whose P2 assembly manifest was
 * fresh before the rename is re-stamped afterwards (the digest labels files by name, and
 * only the names changed); a stale manifest is left stale, so the rename never launders a
 * pending re-assembly.
 *
 * Usage:
 *   npx tsx bin/migrate_proof_filenames.ts <bundle-dir>...      # e.g. ../doc/presentation/<qid>
 *   npx tsx bin/migrate_proof_filenames.ts --all                # every bundle under doc/presentation
 *
 * `--all` covers the bundle directories themselves; a revision workspace copy inside a bundle
 * (`.p5_revision_workspace*`) is out of scope — pass it explicitly if it is ever copied back.
 */
import { existsSync } from "node:fs";
import { readdir, rename } from "node:fs/promises";
import { join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { assertP2AssemblyFresh, recordP2Assembly } from "../src/presentation/assembly_freshness.js";
import { PROOF_DIR, proofFileName, proofObjId } from "../src/presentation/proof_files.js";

async function migrateBundle(outDir: string): Promise<number> {
  const dir = join(outDir, PROOF_DIR);
  const names = await readdir(dir).catch(() => [] as string[]);
  const moves = names
    .filter((n) => n.endsWith(".tex") && n.includes(":"))
    .map((n) => ({ from: n, to: proofFileName(proofObjId(n)!) }));
  if (moves.length === 0) return 0;
  for (const m of moves) if (existsSync(join(dir, m.to))) throw new Error(`${outDir}: both ${m.from} and ${m.to} exist`);
  const fresh = await assertP2AssemblyFresh(outDir).then(() => true, () => false);
  for (const m of moves) await rename(join(dir, m.from), join(dir, m.to));
  if (fresh) await recordP2Assembly(outDir);
  console.log(`${outDir}: renamed ${moves.length} proof file(s)${fresh ? ", assembly manifest re-stamped" : ""}`);
  return moves.length;
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  let bundles: string[];
  if (args.includes("--all")) {
    const root = fileURLToPath(new URL("../../doc/presentation/", import.meta.url));
    bundles = (await readdir(root, { withFileTypes: true })).filter((d) => d.isDirectory()).map((d) => join(root, d.name));
  } else {
    bundles = args.map((a) => resolve(a));
    if (bundles.length === 0) throw new Error("usage: migrate_proof_filenames.ts <bundle-dir>... | --all");
  }
  let total = 0;
  for (const b of bundles) total += await migrateBundle(b);
  console.log(`done: ${total} file(s) renamed across ${bundles.length} bundle(s)`);
}

main().catch((err) => { console.error(err instanceof Error ? err.message : err); process.exit(1); });
