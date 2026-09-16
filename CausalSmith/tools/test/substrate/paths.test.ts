// CausalSmith/tools/test/substrate/paths.test.ts
import { describe, it, expect } from "vitest";
import path from "node:path";
import {
  slugToPascal, substrateRunDir, requirementPath, substrateStatePath,
  substrateLeanDir, substrateModulePrefix, causaleanRoot,
} from "../../src/substrate/paths.js";

// The functions under test build paths with `path.join`, so the expectations must be
// built the same way: a `/`-spelled literal only matches on POSIX, and pinning one
// separator would assert the host's convention rather than the path's structure.
const ROOT = path.join("/ws", "CausalSmith");

describe("substrate paths", () => {
  it("converts slug to PascalCase", () => {
    expect(slugToPascal("bh_affinity")).toBe("BhAffinity");
    expect(slugToPascal("foo-bar_baz")).toBe("FooBarBaz");
  });
  it("builds run-dir + artifact paths under the study folder", () => {
    const run = path.join(ROOT, "doc", "study", "bh_affinity");
    expect(substrateRunDir(ROOT, "bh_affinity")).toBe(run);
    expect(requirementPath(ROOT, "bh_affinity")).toBe(path.join(run, "requirement.md"));
    expect(substrateStatePath(ROOT, "bh_affinity")).toBe(path.join(run, "state.json"));
  });
  it("builds lean staging dir + module prefix", () => {
    expect(substrateLeanDir(ROOT, "bh_affinity"))
      .toBe(path.join(ROOT, "CausalSmith", "Substrate", "BhAffinity"));
    expect(substrateModulePrefix("bh_affinity")).toBe("CausalSmith.Substrate.BhAffinity");
  });
  it("resolves the Causalean root as the parent of repoRoot", () => {
    expect(causaleanRoot(ROOT)).toBe(path.join("/", "ws"));
  });
});
