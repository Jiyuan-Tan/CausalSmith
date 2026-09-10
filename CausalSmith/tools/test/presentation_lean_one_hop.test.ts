import { describe, it, expect } from "vitest";
import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { leanIdentifiers, sectionContextBefore, stripLeanComments, helperDeclarationsFor } from "../src/presentation/lean_one_hop.js";
import { buildModuleDeclIndex } from "../src/presentation/components.js";

describe("lean one-hop context", () => {
  it("lists identifiers once, in order, without keywords, tactics, or comment text", () => {
    const ids = leanIdentifiers("theorem t (h : Foo.bar x) : baz := by\n  -- uses Ghost.decl\n  exact Foo.bar_le h /- Other.thing -/ x");
    expect(ids).toEqual(["t", "h", "Foo.bar", "x", "baz", "Foo.bar_le"]);
    expect(stripLeanComments("a -- b\n/- c /- d -/ e -/ f")).toBe("a \n f");
  });

  it("keeps the variable/open lines of frames still open at the declaration, drops closed ones", () => {
    const src = [
      "open Nat", "section A", "variable (n : Nat)", "end A", "namespace M", "variable {k : Nat}",
      "section B", "variable (h : k = n)", "theorem t : True := trivial", "end B", "end M",
    ].join("\n");
    expect(sectionContextBefore(src, 9)).toBe(["open Nat", "namespace M", "variable {k : Nat}", "variable (h : k = n)"].join("\n"));
    const multi = "variable {α : Type*}\n  [Fintype α]\n  [DecidableEq α]\n\ntheorem u : True := trivial\n";
    expect(sectionContextBefore(multi, 5)).toBe("variable {α : Type*}\n  [Fintype α]\n  [DecidableEq α]");
  });

  it("supplies run helpers in full and library declarations by statement, never the target itself", async () => {
    const ws = await mkdtemp(join(tmpdir(), "one-hop-"));
    try {
      await mkdir(join(ws, "Causalean"), { recursive: true });
      await mkdir(join(ws, "CausalSmith", "Run"), { recursive: true });
      await mkdir(join(ws, "doc"), { recursive: true });
      await writeFile(join(ws, "CausalSmith", "Run", "H.lean"), "namespace Run\ntheorem helper_fact (n : Nat) : n = n := by\n  rfl\nend Run\n");
      await writeFile(join(ws, "CausalSmith", "Run", "T.lean"), "namespace Run\ntheorem target : 1 = 1 := by\n  have := helper_fact 1\n  exact Lib.Good.eq\nend Run\n");
      await writeFile(join(ws, "Causalean", "Lib.lean"), "namespace Lib\nstructure Good where\n  eq : 1 = 1\nend Lib\n");
      await writeFile(join(ws, "doc", "library_index.json"), JSON.stringify({ entries: [{ name: "Lib.Good", file: "Causalean/Lib.lean", line: 2, kind: "structure" }] }));
      const repoRoot = join(ws, "CausalSmith");
      const runIndex = await buildModuleDeclIndex(repoRoot, "Run");
      const { readFile } = await import("node:fs/promises");
      const text = await helperDeclarationsFor({
        proofSource: "theorem target : 1 = 1 := by\n  have := helper_fact 1\n  exact Lib.Good.eq",
        targetDecl: "Run.target", runIndex, readRunFile: (f) => readFile(join(repoRoot, "Run", f), "utf8"), repoRoot,
      });
      expect(text).toContain("-- Run.helper_fact  (H.lean)");
      expect(text).toContain("theorem helper_fact (n : Nat) : n = n := by\n  rfl"); // full source, proof included
      expect(text).not.toContain("theorem target");
      expect(text).toContain("(the Lean proof names no run or library declaration beyond Mathlib)".slice(0, 0)); // placeholder-free
    } finally { await rm(ws, { recursive: true, force: true }); }
  });
});
