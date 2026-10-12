// Tests for `src/shared/codex_json.ts` and the model-output JSON funnels built on it.
//
// A model writes ordinary inline LaTeX into a JSON prose field (`\(d/\epsilon\)`), JSON's
// escape grammar rejects the payload, and a completed stage dies at the finish line. The
// pipeline has several independent model-output parsers, so the escape defense is tested
// three ways: the repair function itself, every funnel against one payload, and a source
// guard over the inventory so a newly added boundary cannot silently reopen the class.
import { describe, expect, it, beforeEach, afterEach } from "vitest";
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parseAgentJson } from "../../src/framework/agent_dispatch.js";
import { extractJsonObject } from "../../src/judgment.js";
import {
  expectStringJsonOutput,
  parseJsonWithEscapeRepair,
  persistCodexRaw,
  repairInvalidStringEscapes,
  tryBraceBalanceRepair,
} from "../../src/shared/codex_json.js";

const srcDir = fileURLToPath(new URL("../../src", import.meta.url));
const binDir = fileURLToPath(new URL("../../bin", import.meta.url));
const emissionsDir = fileURLToPath(new URL("../fixtures/model_emissions", import.meta.url));
const readEmission = (name: string): string => readFileSync(`${emissionsDir}/${name}`, "utf8");

let tmp: string;
beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "cs-codex-json-"));
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

describe("expectStringJsonOutput", () => {
  it("parses a well-formed object", () => {
    expect(expectStringJsonOutput('{"a":1}')).toEqual({ a: 1 });
  });

  it("slices between first { and last } when wrapped in prose / fences", () => {
    const wrapped = '```json\n{"x":[1,2,3]}\n```';
    expect(expectStringJsonOutput(wrapped)).toEqual({ x: [1, 2, 3] });
  });

  it("returns the FIRST balanced object when codex double-emits", () => {
    // Failure mode observed in research pipeline: codex emits a pretty-printed
    // object followed by a compact restatement. Previous behavior: first-{/last-}
    // slice produced the concatenation, which JSON.parse rejects.
    const double = '{"a":1,"b":[2,3]}\n{"a":1,"b":[2,3]}';
    expect(expectStringJsonOutput(double)).toEqual({ a: 1, b: [2, 3] });
  });

  it("parses a fenced JSON object followed by trailing prose", () => {
    const messy = '```json\n{"verdict":"pass","notes":"ok"}\n```\nAnd here is some commentary.';
    expect(expectStringJsonOutput(messy)).toEqual({ verdict: "pass", notes: "ok" });
  });

  it("repairs a 1-char truncation (missing outer })", () => {
    // Mirror the Manski 1990 failure mode: one missing closing brace.
    const truncated = '{"insight":{"id":"x","theorems":[{"t":1}]}';
    expect(expectStringJsonOutput(truncated)).toEqual({
      insight: { id: "x", theorems: [{ t: 1 }] },
    });
  });

  it("repairs missing ] before missing }", () => {
    const truncated = '{"a":[1,2,3';
    expect(expectStringJsonOutput(truncated)).toEqual({ a: [1, 2, 3] });
  });

  it.each([
    ["an unrepairable parse failure", '{"a": "uncl'],
    ["output with no object at all", "just prose, no braces here"],
  ])("tags %s with code codex_malformed_output", (_label, stdout) => {
    try {
      expectStringJsonOutput(stdout);
      throw new Error("expected throw");
    } catch (err: unknown) {
      expect((err as { code?: string }).code).toBe("codex_malformed_output");
    }
  });

  it("does NOT 'repair' over-balanced inputs (extra closers)", () => {
    // Over-balanced: heuristic must bail out, not silently produce something.
    expect(tryBraceBalanceRepair('{"a":1}}')).toBeNull();
  });

  it("does NOT repair inputs missing more than 3 closers (likely structural)", () => {
    const tooBroken = "{".repeat(5) + '"a":1';
    expect(tryBraceBalanceRepair(tooBroken)).toBeNull();
  });

  it("ignores brackets inside strings when counting", () => {
    // Balanced object whose string content has dangling braces. Must NOT be
    // treated as needing repair.
    const s = '{"text":"some {prose with [brackets]} inside"}';
    expect(tryBraceBalanceRepair(s)).toBeNull();
    expect(expectStringJsonOutput(s)).toEqual({
      text: "some {prose with [brackets]} inside",
    });
  });
});

describe("persistCodexRaw", () => {
  it("persistCodexRaw writes the raw payload under codex_raw/", async () => {
    const written = await persistCodexRaw(tmp, "passA", "any stdout bytes");
    expect(written).not.toBeNull();
    expect(existsSync(written!)).toBe(true);
    expect(readFileSync(written!, "utf8")).toBe("any stdout bytes");
    const dir = path.join(tmp, "codex_raw");
    const entries = readdirSync(dir);
    expect(entries.length).toBe(1);
    expect(entries[0]).toMatch(/^passA__/);
  });

  it("persistCodexRaw sanitizes tag and never throws on bad run dirs", async () => {
    // Embed a NUL byte so mkdir is guaranteed to reject the path on every OS
    // (recursive mkdir is otherwise permissive — "/nonexistent/..." would
    // succeed on Windows by anchoring under the current drive).
    const written = await persistCodexRaw("bad\0dir", "tag with spaces?", "x");
    expect(written).toBeNull();
  });
});

describe("repairInvalidStringEscapes", () => {
  it.each([
    // `\(` is a legal LaTeX delimiter and an illegal JSON escape.
    ["LaTeX inline math", String.raw`{"v":"shells \(q_d(P)=r_n\), with the converse"}`,
      String.raw`shells \(q_d(P)=r_n\), with the converse`],
    // Models mix both spellings in one string; the valid escapes must survive as they are.
    ["a string mixing valid and invalid escapes", String.raw`{"v":"\(x\) and \\le and \n done"}`,
      "\\(x\\) and \\le and \n done"],
    // `\u` is a valid PREFIX but `\usep` is not a valid escape.
    ["\\usepackage", String.raw`{"v":"\usepackage{amsmath}"}`, String.raw`\usepackage{amsmath}`],
  ])("repairs %s", (_label, raw, expected) => {
    expect(() => JSON.parse(raw)).toThrow();
    expect(JSON.parse(repairInvalidStringEscapes(raw)!).v).toBe(expected);
  });

  it.each([
    // Re-escaping an already-escaped backslash would corrupt it.
    ["an already-escaped backslash", String.raw`{"v":"c_G \\le 3/16"}`, String.raw`c_G \le 3/16`],
    ["a genuine \\uXXXX escape", String.raw`{"v":"é"}`, "é"],
    ["a payload with no string values", `{"v":1}`, 1],
    ["plain text", `{"v":"plain text"}`, "plain text"],
  ])("returns null for %s", (_label, raw, expected) => {
    expect(repairInvalidStringEscapes(raw)).toBeNull();
    expect(JSON.parse(raw).v).toBe(expected);
  });

  it("cannot change structure — only string contents", () => {
    // A repair that could alter structure might make a parse succeed DIFFERENTLY,
    // which is worse than failing.
    const raw = String.raw`{"a":"\(","b":[1,2],"c":{"d":"\)"}}`;
    const parsed = JSON.parse(repairInvalidStringEscapes(raw)!);
    expect(parsed.b).toEqual([1, 2]);
    expect(parsed.c.d).toBe("\\)");
    expect(Object.keys(parsed)).toEqual(["a", "b", "c"]);
  });
});

describe("extractJsonObject — escape repair at the funnel", () => {
  it("handles the mixed-spelling case models actually emit (raw `\\(` beside escaped `\\\\le`)", () => {
    const raw = String.raw`{"critique":"Since \(x\) satisfies \\le 1, the bound \sum_i w_i holds."}`;
    const out = extractJsonObject(raw) as Record<string, unknown>;
    expect(String(out.critique)).toContain(String.raw`\(x\)`);
    expect(String(out.critique)).toContain(String.raw`\le 1`);
    expect(String(out.critique)).toContain(String.raw`\sum_i`);
  });

  it("repairs the BALANCED slice, not just the legacy first-{/last-} fallback", () => {
    // Isolates the balanced-object scan. The legacy fallback slices first `{` to last `}`,
    // so trailing prose braces make it produce a slice that is not the payload; only
    // repairing the balanced candidate itself recovers the verdict here.
    const raw =
      String.raw`{"verdict":"PASS","note":"the \(d/\epsilon\) term dominates"}` +
      "\nFollow-up: consider the set {x | P x} next round.";
    const out = extractJsonObject(raw) as Record<string, unknown>;
    expect(out.verdict).toBe("PASS");
    expect(String(out.note)).toContain(String.raw`\(d/\epsilon\)`);
  });

  it("still finds the real object when prose braces precede it (no regression)", () => {
    const text = 'Considering the set {x | P x} we conclude:\n{"route":"stage_0","reason":"r"}';
    expect(extractJsonObject(text)).toEqual({ route: "stage_0", reason: "r" });
  });

  it("still throws on genuinely malformed output, reporting the ORIGINAL parse error", () => {
    // Unrepairable by escapes: a structural fault must not be masked or relabelled.
    expect(() => extractJsonObject('{"a": 1, "b": }')).toThrow();
  });
});

describe("the repair is a strict extension of JSON.parse", () => {
  // The safety argument for wiring this into a funnel shared with F-stage payloads
  // (which embed Lean source) is that the repair fires ONLY on bytes JSON.parse already
  // rejects. So on anything that parsed before, it must be a bit-for-bit no-op.
  it("is identical to JSON.parse on already-valid payloads", () => {
    const valid = [
      String.raw`{"a":"plain"}`,
      String.raw`{"tex":"\\alpha + \\beta"}`,
      String.raw`{"multi":"line one\nline two\ttabbed"}`,
      String.raw`{"unicode":"\u00e9 caf\u00e9"}`,
      String.raw`{"path":"C:\\Users\\x"}`,
      String.raw`{"nested":{"arr":[1,2,{"k":"\\frac{1}{2}"}]}}`,
      String.raw`{"quoted":"he said \"hi\""}`,
      String.raw`{"solidus":"a\/b"}`,
    ];
    for (const v of valid) {
      expect(parseJsonWithEscapeRepair(v), `changed under repair: ${v}`).toEqual(JSON.parse(v));
      expect(extractJsonObject(v), `changed under funnel: ${v}`).toEqual(JSON.parse(v));
    }
  });

  it("leaves an F-stage Lean payload untouched", () => {
    // F-stage outputs embed Lean source; the funnel is shared with them, so a repair
    // that reinterpreted this content would be far worse than the parse error it fixes.
    const lean = {
      decl: "theorem foo (x : ℝ) : x ≤ x := le_refl x",
      body: 'by\n  simp [Set.mem_setOf_eq]\n  exact ⟨h₁, h₂⟩',
      doc: "/-- The bound \\(x \\le x\\). -/",
    };
    const serialized = JSON.stringify(lean);
    expect(parseJsonWithEscapeRepair(serialized)).toEqual(lean);
    expect(extractJsonObject(serialized)).toEqual(lean);
  });

  it("is idempotent on a repaired payload", () => {
    const raw = String.raw`{"critique":"bound \(d/\epsilon\)"}`;
    const once = extractJsonObject(raw);
    expect(extractJsonObject(JSON.stringify(once))).toEqual(once);
  });
});

describe("every model-output parser carries the escape defense", () => {
  // The repair must be present in EVERY parser, so assert the property directly: adding a
  // parser without it is a red test.
  it("all model-output funnels survive the same inline-math payload", () => {
    const raw = String.raw`{"verdict":"PASS","note":"the \(d/\epsilon\) term"}`;
    // Non-vacuity: this must genuinely defeat a plain parse, or the test proves nothing.
    expect(() => JSON.parse(raw), "fixture does not reproduce the fault").toThrow();
    const funnels: Array<[string, (s: string) => unknown]> = [
      ["extractJsonObject", extractJsonObject],
      ["parseJsonWithEscapeRepair", parseJsonWithEscapeRepair],
      ["expectStringJsonOutput", expectStringJsonOutput],
      ["parseAgentJson", (s) => parseAgentJson(s).json],
    ];
    for (const [name, parse] of funnels) {
      const out = parse(raw) as Record<string, unknown>;
      expect(out?.verdict, `${name} lost the payload`).toBe("PASS");
      // The LaTeX must survive intact — a repair that mangled the prose would be its own bug.
      expect(String(out?.note), `${name} mangled the prose`).toBe(String.raw`the \(d/\epsilon\) term`);
    }
  });
});

// Captured emissions, not synthetic ones: a stub only ever emits what we thought to write.
// Capture at failure time — once a stage is re-run its log's final emission is a successful
// one, and the failing payload is gone.
describe("recorded model emissions — production parser", () => {
  it("recovers the D0.5.G verdict whose critique carried raw LaTeX", () => {
    const raw = readEmission("d05g_latex_in_json.txt");
    // Non-vacuity: the payload must genuinely defeat a plain parse, or this proves nothing.
    // This is verbatim the error the live run died on:
    //   causalsmith: Bad escaped character in JSON at position 213
    expect(() => JSON.parse(raw), "fixture does not reproduce the fault").toThrow(/Bad escaped character/);

    const out = expectStringJsonOutput(raw) as Record<string, unknown>;
    expect(out.tier).toBe("field");
    expect(out.flagship_potential).toBe(false);
    // The LaTeX must survive intact — a repair that mangled the prose would be its own bug.
    expect(String(out.critique)).toContain("\\(q_d(P)=r_n\\)");
    // The model mixed spellings in ONE string: `\(` raw, `\\le` correctly escaped.
    expect(String(out.critique)).toContain("\\le");
  });

  it("parses every captured emission", () => {
    const files = readdirSync(emissionsDir).filter((f) => f.endsWith(".txt"));
    expect(files.length, "no fixtures captured").toBeGreaterThan(0);
    for (const f of files) {
      expect(() => expectStringJsonOutput(readEmission(f)), `failed to parse ${f}`).not.toThrow();
    }
  });

  it("leaves already-valid emissions byte-identical after parsing", () => {
    // The escape repair must be a no-op on well-formed output; a parser that silently
    // rewrites correct payloads would corrupt verdicts nobody was worried about.
    for (const f of readdirSync(emissionsDir).filter((n) => n.startsWith("clean_"))) {
      const raw = readEmission(f);
      expect(expectStringJsonOutput(raw), `${f} changed under the parser`).toEqual(JSON.parse(raw));
    }
  });
});

describe("source guard — no bare JSON.parse at a model-output boundary", () => {
  // A call site is only safe if the escape defense is visible ON that expression.
  const DEFENSES = [
    "parseJsonWithEscapeRepair",
    "normalizeRawModelJson",
    "parseRepairedModelJson",
    "readRepairedModelJson",
    "readTypedCore",
    "repairInvalidStringEscapes",
    "extractJsonObject",
    "expectStringJsonOutput",
    "parseJsonLoose",
  ];
  // Expressions that identify a MODEL-authored source: agent stdout, or a file an agent
  // wrote itself. Pipeline-written state (state.json, caches, stores) is deliberately
  // excluded — those are re-serialized by us and fail loud by design.
  const MODEL_SOURCES = [
    /\bstdout\b/,
    /\bout\.stdout\b/,
    /paths\.plan\b/,
    /\bplanPath\b/,
    /\bverdictFile\b/,
    // No leading \b: these appear as suffixes of longer identifiers (`absoluteSolvePath`).
    /SolvePath\b/,
    /solveJsonPath\b/,
  ];

  const walk = (dir: string): string[] =>
    readdirSync(dir).flatMap((name) => {
      const p = path.join(dir, name);
      return statSync(p).isDirectory() ? walk(p) : p.endsWith(".ts") ? [p] : [];
    });

  it("has no unguarded JSON.parse over agent stdout or an agent-written plan", () => {
    const offenders: string[] = [];
    for (const file of [...walk(srcDir), ...walk(binDir)]) {
      readFileSync(file, "utf8").split("\n").forEach((line, i) => {
        if (!line.includes("JSON.parse(")) return;
        if (!MODEL_SOURCES.some((re) => re.test(line))) return;
        if (DEFENSES.some((d) => line.includes(d))) return;
        const rel = file.startsWith(srcDir) ? `src/${file.slice(srcDir.length + 1)}` : `bin/${file.slice(binDir.length + 1)}`;
        offenders.push(`${rel}:${i + 1}: ${line.trim()}`);
      });
    }
    expect(
      offenders,
      "Model-authored JSON must go through the escape defense — a raw LaTeX backslash " +
        "otherwise kills the whole payload. Wrap the read in parseJsonWithEscapeRepair (any " +
        "model output) or normalizeRawModelJson (known-TeX D-stage boundaries).",
    ).toEqual([]);
  });
});
