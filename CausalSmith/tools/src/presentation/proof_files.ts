/**
 * Portable file names for the per-object appendix proofs a bundle caches under `proofs/`.
 *
 * Object ids are LaTeX labels such as `thm:convex-design`, and `:` is not a legal file-name
 * character on Windows — a bundle written as `proofs/<obj_id>.tex` cannot even be checked out
 * there. The file name therefore spells the colon as `--` (`proofs/thm--convex-design.tex`);
 * ids never contain `--`, so the encoding is invertible. Any other non-portable character in
 * an id is an error at write time rather than an unreadable checkout later.
 *
 * Bundles written before this encoding keep working: `proofFilePath` resolves the encoded
 * name first and falls back to the legacy `<obj_id>.tex` when only that exists, so an
 * unmigrated bundle stays internally consistent (its reads and writes hit the same file).
 * `bin/migrate_proof_filenames.ts` renames a bundle in place.
 */
import { existsSync } from "node:fs";
import { join } from "node:path";

export const PROOF_DIR = "proofs";

const PORTABLE_NAME = /^[A-Za-z0-9._-]+$/;

/** `thm:convex-design` → `thm--convex-design.tex`. Throws on an id no portable file name spells. */
export function proofFileName(objId: string): string {
  if (objId.includes("--")) throw new Error(`object id ${JSON.stringify(objId)} contains "--", which encodes ":" in proof file names`);
  const stem = objId.replace(/:/g, "--");
  if (!PORTABLE_NAME.test(stem)) throw new Error(`object id ${JSON.stringify(objId)} has no portable proof file name`);
  return `${stem}.tex`;
}

/** Inverse of `proofFileName` (also accepts a legacy `<obj_id>.tex`); `null` for any other file. */
export function proofObjId(fileName: string): string | null {
  if (!fileName.endsWith(".tex") || fileName.startsWith("_")) return null;
  return fileName.slice(0, -".tex".length).replace(/--/g, ":");
}

/** The proof file for `objId` under `outDir/proofs/`: the encoded name, or the legacy `<obj_id>.tex` when only that exists. */
export function proofFilePath(outDir: string, objId: string): string {
  const encoded = join(outDir, PROOF_DIR, proofFileName(objId));
  if (existsSync(encoded)) return encoded;
  const legacy = join(outDir, PROOF_DIR, `${objId}.tex`);
  return legacy !== encoded && existsSync(legacy) ? legacy : encoded;
}
