// Resolve the Python 3 interpreter that runs the retrieval scripts
// (scripts/embed_text.py, scripts/rerank_query.py, scripts/embed_library.py, …).
//
// Why this is not just the literal string "python3": that name does not exist on
// Windows. Python for Windows installs `python.exe` plus the `py.exe` launcher, and a
// bare `python3` there either fails to resolve or hits the Microsoft Store
// app-execution-alias stub — which is why the semantic retrieval tier could never run
// on Windows even with the model weights in place.
//
// Resolution order (first working candidate wins, cached for the process):
//   1. CAUSALSMITH_PYTHON env var        — an explicit interpreter path
//   2. `pythonPath` in config/local.json — the same, per machine
//   3. platform candidates, probed       — POSIX: python3, python
//                                          Windows: python, py -3, python3
// On Windows `python` is probed BEFORE `py -3` on purpose: an activated venv puts its
// own `python` first on PATH, while `py -3` would silently bypass it and run the
// system interpreter — which is very likely the one WITHOUT torch installed.
//
// A candidate counts as working only if it prints its major version as "3": the Store
// alias stub and a python2 both fail that, so neither is ever selected.
import { execFileSync } from "node:child_process";
import { localConfig } from "../local_config.js";

export interface PythonCommand {
  /** Executable to spawn. */
  bin: string;
  /** Arguments that must precede the script path (e.g. `-3` for the `py` launcher). */
  prefixArgs: string[];
}

const CANDIDATES: PythonCommand[] =
  process.platform === "win32"
    ? [
        { bin: "python", prefixArgs: [] },
        { bin: "py", prefixArgs: ["-3"] },
        { bin: "python3", prefixArgs: [] },
      ]
    : [
        { bin: "python3", prefixArgs: [] },
        { bin: "python", prefixArgs: [] },
      ];

/** True when `cmd` is a working Python 3. Never throws. */
export function probePython(cmd: PythonCommand): boolean {
  try {
    const out = execFileSync(
      cmd.bin,
      [...cmd.prefixArgs, "-c", "import sys; print(sys.version_info[0])"],
      { timeout: 20_000, stdio: ["ignore", "pipe", "ignore"], encoding: "utf8" },
    );
    return out.trim() === "3";
  } catch {
    return false;
  }
}

let cached: PythonCommand | null | undefined;

/**
 * The resolved Python 3 command, or null when no working interpreter was found.
 * Callers that can degrade (the semantic / reranker tiers fall back to lexical)
 * should branch on null rather than letting a spawn failure surface as a crash.
 */
export function tryPythonCommand(): PythonCommand | null {
  if (cached !== undefined) return cached;
  const override = process.env.CAUSALSMITH_PYTHON?.trim() || localConfig().pythonPath?.trim();
  if (override && !probePython({ bin: override, prefixArgs: [] })) {
    // Never fall through to the platform defaults in silence: the override exists
    // precisely because the default interpreter is the wrong one (no torch), so a
    // quiet fallback degrades retrieval to lexical with no visible cause.
    console.warn(
      `[python] configured interpreter "${override}" is not a working Python 3; ` +
        "falling back to the platform defaults, which may lack torch/sentence-transformers. " +
        "On Windows point pythonPath at the interpreter's .exe — execFileSync cannot run " +
        "a .bat/.cmd shim (e.g. pyenv-win's python.bat).",
    );
  } else if (override) {
    cached = { bin: override, prefixArgs: [] };
    return cached;
  }
  cached = CANDIDATES.find(probePython) ?? null;
  return cached;
}

/** As `tryPythonCommand`, but throws with an actionable message instead of returning null. */
export function pythonCommand(): PythonCommand {
  const cmd = tryPythonCommand();
  if (cmd) return cmd;
  throw new Error(
    "No working Python 3 found for the retrieval scripts (tried: " +
      CANDIDATES.map((c) => [c.bin, ...c.prefixArgs].join(" ")).join(", ") +
      "). Install Python 3 with torch + sentence-transformers, or set CAUSALSMITH_PYTHON " +
      "(or `pythonPath` in tools/config/local.json) to the interpreter that has them.",
  );
}

/** Spawn arguments for running `script` with `args`: `[bin, [...prefixArgs, script, ...args]]`. */
export function pythonArgs(script: string, args: string[] = []): [string, string[]] {
  const cmd = pythonCommand();
  return [cmd.bin, [...cmd.prefixArgs, script, ...args]];
}

/** Test seam: drop the memoized interpreter so a later call re-probes. */
export function resetPythonCache(): void {
  cached = undefined;
}
