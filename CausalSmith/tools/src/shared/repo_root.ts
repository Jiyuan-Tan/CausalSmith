// Canonical root resolution for every entry point.
//
// WHY THIS EXISTS. `findRepoRoot` was copy-pasted into 30 files in 11 behavioural
// variants, and they did not agree on what they returned:
//
//   strict  walk up for `lakefile.toml` with `name = "CausalSmith"`; throw if absent
//   loose   walk up for ANY `lakefile.lean`/`lakefile.toml`; return the FIRST hit,
//           and on failure `return start` — silently using the caller's cwd
//
// The workspace root carries its own `lakefile.toml` with `name = "Causalean"`, so a
// loose caller invoked from outside `CausalSmith/` resolved to the CAUSALEAN package
// and then wrote CausalSmith artifacts under the wrong tree — a fail-open with no
// diagnostic, in 14+ operator CLIs.

import { existsSync, readFileSync } from "node:fs";
import path from "node:path";

/** Locate the CausalSmith PACKAGE root — the directory whose `lakefile.toml`
 *  declares `name = "CausalSmith"`. This is the `repoRoot` every pipeline context,
 *  `artifactPath` call, and state file is resolved against.
 *
 *  Throws rather than falling back to `start`: a wrong root does not fail loudly at
 *  the point of error, it silently writes a run's artifacts into another package.
 *
 *  @param start directory to search upward from (default: `process.cwd()`) */
export function findCausalSmithRoot(start: string = process.cwd()): string {
  let cur = path.resolve(start);
  for (;;) {
    const lakefile = path.join(cur, "lakefile.toml");
    if (existsSync(lakefile)) {
      try {
        if (/^\s*name\s*=\s*"CausalSmith"/m.test(readFileSync(lakefile, "utf8"))) return cur;
      } catch {
        // Unreadable lakefile: keep walking rather than claiming this directory.
      }
    }
    const parent = path.dirname(cur);
    if (parent === cur) {
      throw new Error(
        `Could not locate the CausalSmith package root from ${start} — no lakefile.toml with ` +
          `name = "CausalSmith" in any parent directory. Run from inside the CausalSmith package ` +
          `or one of its subdirectories.`,
      );
    }
    cur = parent;
  }
}
