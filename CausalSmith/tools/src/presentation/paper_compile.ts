/**
 * The two mechanical steps every paper compile shares: refresh the template-owned macros, then
 * run `latexmk`.
 *
 * ## Why they live here rather than inside P4
 *
 * `restamp.ts` exists to reproduce a bundle's PDF byte-for-byte apart from the stamp values, and
 * it must therefore compile it **exactly** the way P4 does — same template copy, same `latexmk`
 * argv, same working directory, same buffer. Expressed as "mirror what P4 does" that is a comment
 * two files apart from the code it describes, and the first divergence would show up as a restamp
 * that silently produces a different PDF from the emit. Expressed as one function both callers
 * invoke, it cannot diverge at all.
 *
 * Nothing here knows about the pipeline's types, so the restamp tool and the Zenodo release
 * command can compile a bundle without importing a stage.
 */
import { execFile } from "node:child_process";
import { readFile, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { promisify } from "node:util";

const execFileP = promisify(execFile);

/** Template-owned macro file, refreshed into the bundle on every emit and every restamp. */
export const MACROS_FILE = "paper_macros.tex";

/** The compile, as it has always been run. Change it here or not at all. */
export const LATEXMK_ARGV = ["-pdf", "-interaction=nonstopmode", "paper.tex"] as const;

/** `latexmk` can emit a great deal on a failing run; the cap is generous enough that the real
 *  error is never the thing that got truncated by the pipe. */
const MAX_BUFFER = 64 * 1024 * 1024;

/**
 * Copy the template's `paper_macros.tex` into `outDir`.
 *
 * P4 is the supported deterministic re-emit entrypoint and restamp is the supported
 * recompile-only entrypoint, so BOTH must take the template-owned macros from the template
 * rather than inheriting whatever copy P2 last wrote. Otherwise a layout fix that shipped with
 * the template reaches some bundles and not others, and a compile failure caused only by a stale
 * copy looks like a failure of the paper.
 */
export async function refreshPaperMacros(outDir: string): Promise<void> {
  const macros = await readFile(join(import.meta.dirname, "templates", MACROS_FILE), "utf8");
  await writeFile(join(outDir, MACROS_FILE), macros, "utf8");
}

/**
 * Thrown when `latexmk` exits non-zero. It carries the RAW combined output rather than a
 * pre-formatted message, because the two callers frame it differently: P4 tells the orchestrator
 * to repair the authored source, while restamp reports the bundle as failed and leaves the real
 * directory untouched.
 */
export class LatexCompileError extends Error {
  readonly code = "latex_compile_failed";
  constructor(readonly outDir: string, readonly log: string) {
    super(`latexmk failed in ${outDir}`);
    this.name = "LatexCompileError";
  }
}

/** Run `latexmk -pdf` over `paper.tex` in `outDir`. */
export async function compilePaper(outDir: string): Promise<void> {
  try {
    await execFileP("latexmk", [...LATEXMK_ARGV], { cwd: outDir, maxBuffer: MAX_BUFFER });
  } catch (e: unknown) {
    const err = e as { stdout?: string; stderr?: string; message?: string };
    throw new LatexCompileError(outDir, [err.stdout, err.stderr, err.message].filter(Boolean).join("\n"));
  }
}
