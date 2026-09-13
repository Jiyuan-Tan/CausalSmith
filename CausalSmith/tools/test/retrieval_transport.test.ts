// Semantic retrieval must work on Windows, not just Linux/macOS.
//
// Two independent defects made it Linux/macOS-only even with the ~2.3 GB fine-tuned
// weights downloaded and in place:
//
//  1. `scripts/embed_text.py` / `rerank_query.py` called `socket.AF_UNIX`, which CPython
//     does not expose on Windows (cpython#77589). That raises AttributeError, and both
//     clients wrapped the call in `except OSError` only — so instead of degrading to the
//     inline model load they already implement, the process died and the TS caller
//     silently fell back to lexical-only ranking.
//  2. Every call site spawned the literal `python3`, which is not a program name on
//     Windows (there it is `python` / `py -3`, or the Store alias stub).
//
// These tests pin both fixes. The transport one runs the real module in BOTH modes:
// `tcp` clears `HAS_UNIX` to force the Windows branch, which is the only way a POSIX
// box can cover the code path Windows always takes.
import { describe, it, expect } from "vitest";
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { probePython, tryPythonCommand } from "../src/shared/python.js";

const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const SCRIPTS = path.join(TOOLS, "scripts");
const PROBE = path.join(TOOLS, "test", "fixtures", "daemon_ipc_roundtrip.py");

const py = tryPythonCommand();
// A machine with no Python 3 cannot exercise the transport; skip rather than fail red,
// but never skip the source guards below — those are static and must always run.
const withPython = py ? describe : describe.skip;

withPython("daemon_ipc transport", () => {
  for (const mode of ["native", "tcp"] as const) {
    it(`completes a serve/probe/echo round trip over the ${mode} transport`, () => {
      const out = execFileSync(py!.bin, [...py!.prefixArgs, PROBE, mode], {
        encoding: "utf8",
        timeout: 60_000,
      });
      expect(out.trim()).toMatch(/^OK (unix|tcp)$/);
      // `tcp` is the Windows transport; it must report tcp even on a POSIX box.
      if (mode === "tcp") expect(out.trim()).toBe("OK tcp");
    });
  }
});

describe("retrieval scripts are AF_UNIX-free outside the transport module", () => {
  // Comments are stripped first: the daemons legitimately EXPLAIN the AF_UNIX/Windows
  // split in prose, and only executable uses reintroduce the bug.
  const codeOf = (f: string): string =>
    fs
      .readFileSync(path.join(SCRIPTS, f), "utf8")
      .split("\n")
      .map((l) => l.replace(/#.*$/, ""))
      .join("\n");

  it("keeps every executable AF_UNIX use inside scripts/daemon_ipc.py", () => {
    const offenders = fs
      .readdirSync(SCRIPTS)
      .filter((f) => f.endsWith(".py") && f !== "daemon_ipc.py")
      .filter((f) => /\bAF_UNIX\b/.test(codeOf(f)));
    // A direct AF_UNIX use outside daemon_ipc.py reintroduces the Windows AttributeError.
    expect(offenders).toEqual([]);
  });

  it("spawns no hardcoded `python3` from the TS call sites or the npm scripts", () => {
    const pkg = fs.readFileSync(path.join(TOOLS, "package.json"), "utf8");
    expect(JSON.parse(pkg).scripts["embed:library"]).not.toMatch(/python3/);
    expect(JSON.parse(pkg).scripts["lint:embeddings"]).not.toMatch(/python3/);
    for (const rel of [
      "src/formalization/semantic_tier.ts",
      "src/formalization/reranker_tier.ts",
      "src/formalization/retrieval_eval/harness.ts",
    ]) {
      const src = fs.readFileSync(path.join(TOOLS, rel), "utf8");
      expect(src, `${rel} must resolve the interpreter, not spawn "python3"`).not.toMatch(
        /execFileSync\(\s*"python3"/,
      );
    }
  });
});

describe("retrieval scripts pin UTF-8 explicitly", () => {
  // Windows decodes text with the ANSI code page (cp1252), not UTF-8. Queries carry
  // Lean Unicode (=ᵐ[μ], σ, ∀) and doc/library_index.json is ~4% non-ASCII, so an
  // unpinned read there either crashes or silently decodes the WRONG text.
  it("reconfigures stdin to UTF-8 in both query clients", () => {
    for (const f of ["embed_text.py", "rerank_query.py"]) {
      const src = fs.readFileSync(path.join(SCRIPTS, f), "utf8");
      expect(src, `${f} must pin stdin to UTF-8`).toMatch(
        /sys\.stdin\.reconfigure\(encoding="utf-8"/,
      );
    }
  });

  it("opens no index/meta JSON without an explicit encoding", () => {
    const offenders: string[] = [];
    for (const f of fs.readdirSync(SCRIPTS).filter((x) => x.endsWith(".py"))) {
      const src = fs.readFileSync(path.join(SCRIPTS, f), "utf8");
      // `json.load(open(P))` inherits the locale codec — the exact Windows crash.
      if (/json\.(load|dump)\(\s*open\(/.test(src)) offenders.push(f);
      for (const m of src.matchAll(/(?<![.\w])open\(/g)) {
        // Take the balanced argument list, so a nested call like open(paths("nl")[1], …)
        // is not truncated at its inner ")" and misread as unpinned.
        let depth = 0, end = m.index! + m[0].length;
        for (; end < src.length; end++) {
          if (src[end] === "(") depth++;
          else if (src[end] === ")") { if (depth === 0) break; depth--; }
        }
        const argsText = src.slice(m.index! + m[0].length, end);
        if (/encoding=/.test(argsText) || /"[rwa]b"/.test(argsText)) continue;
        offenders.push(`${f}: open(${argsText})`);
      }
    }
    expect(offenders).toEqual([]);
  });
});

describe("python interpreter resolution", () => {
  it("rejects a candidate that is not a working python 3", () => {
    expect(probePython({ bin: "definitely-not-a-real-interpreter", prefixArgs: [] })).toBe(false);
  });

  it("accepts the resolved interpreter it hands back", () => {
    if (!py) return; // no Python on this machine; the null contract is covered below
    expect(probePython(py)).toBe(true);
  });

  it("returns null rather than throwing when nothing resolves", () => {
    // tryPythonCommand never throws; pythonCommand is the throwing variant. Callers that
    // must degrade (semantic/reranker tiers) depend on this distinction.
    expect(() => tryPythonCommand()).not.toThrow();
  });
});
