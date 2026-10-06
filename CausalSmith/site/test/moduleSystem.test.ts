import { describe, expect, it } from "vitest";
import { readFileSync, rmSync, writeFileSync } from "node:fs";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { sourceKind } from "../src/lib/library.js";
import {
  isDefinitionLike,
  isInductiveLike,
  isInstanceLike,
  isRecordLike,
} from "../src/lib/leanCards.js";
import {
  generateRedirectArtifact,
  libraryPagePaths,
  loadRedirectArtifact,
  redirectsFromManifest,
} from "../scripts/gen_redirects.mjs";

describe("module-system declaration headers", () => {
  it("finds a public theorem in library source", () => {
    expect(sourceKind({ kind: "lemma", source: "@[expose] public theorem x : True := trivial" })).toBe("theorem");
  });

  it("finds a public def", () => {
    expect(isDefinitionLike("public def x := 1")).toBe(true);
  });

  it("finds a public structure", () => {
    expect(isRecordLike("public structure X where\n  value : Nat")).toBe(true);
  });

  it("finds a public instance", () => {
    expect(isInstanceLike("public instance : Inhabited Nat := ⟨0⟩")).toBe(true);
  });

  it("finds a public inductive", () => {
    expect(isInductiveLike("public inductive X where\n  | mk")).toBe(true);
  });

  it("keeps the paper formalization header matcher module-aware", () => {
    const page = readFileSync(join(process.cwd(), "src/pages/papers/[id]/formalization.astro"), "utf8");
    expect(page).toContain("public\\s+");
    expect(page).toContain("meta\\s+");
    expect(/(?:^|\n)\s*(?:@\[[^\]]*\]\s*)*(?:public\s+|private\s+|protected\s+|meta\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance)\b/.exec("public theorem x : True := trivial")?.[1]).toBe("theorem");
  });
});

describe("library move redirects", () => {
  const manifest = {
    moves: [
      { kind: "move", from: "Causalean.PO.Old.Basic", to: "Causalean.Stat.New.Basic", since: "2026-09-13", shim: true },
      { kind: "move", from: "Causalean.PO.Old.Main", to: "Causalean.Stat.New.Main", since: "2026-09-13", shim: true },
      { kind: "move", from: "Causalean.Stat.New.Basic", to: "Causalean.Stat.Final.Basic", since: "2026-09-13", shim: true },
      { kind: "move", from: "Causalean.Stat.New.Main", to: "Causalean.Stat.Final.Main", since: "2026-09-13", shim: true },
    ],
    grandfathered_600_900: [],
  };
  const currentModules = ["Causalean.PO.Live", "Causalean.Stat.Final.Basic", "Causalean.Stat.Final.Main"];

  it("coalesces old-directory moves to the common live destination", () => {
    expect(libraryPagePaths(currentModules)).toContain("/library/Stat/Final");
    expect(redirectsFromManifest(manifest, currentModules)).toEqual({
      "/library/PO/Old": "/library/Stat/Final",
      "/library/Stat/New": "/library/Stat/Final",
    });
  });

  it("prefers an explicit parent move when one child moves to another layer", () => {
    const parentMove = {
      moves: [
        {
          kind: "move",
          from: "Causalean.Stat.Coupling.ProductLossMonotoneCoupling",
          to: "Causalean.Stat.Coupling.Monotone.ProductLoss",
        },
        {
          kind: "move",
          from: "Causalean.Stat.Coupling.ProductLossMonotoneCoupling.Coupling",
          to: "Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling",
        },
        {
          kind: "move",
          from: "Causalean.Stat.Coupling.ProductLossMonotoneCoupling.TailIntegral",
          to: "Causalean.Mathlib.Analysis.SignedTailRepresentation",
        },
      ],
    };
    const modules = [
      "Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling",
      "Causalean.Mathlib.Analysis.SignedTailRepresentation",
    ];
    expect(redirectsFromManifest(parentMove, modules)).toEqual({
      "/library/Stat/Coupling/ProductLossMonotoneCoupling":
        "/library/Stat/Coupling/Monotone/ProductLoss",
    });
  });

  it("falls back to child coalescing when the explicit parent destination is unavailable", () => {
    const unavailableParent = {
      moves: [
        { kind: "move", from: "Causalean.PO.Old", to: "Causalean.Gone.Parent" },
        { kind: "move", from: "Causalean.PO.Old.Basic", to: "Causalean.Stat.Final.Basic" },
        { kind: "move", from: "Causalean.PO.Old.Main", to: "Causalean.Stat.Final.Main" },
      ],
    };
    expect(redirectsFromManifest(unavailableParent, currentModules)).toEqual({
      "/library/PO/Old": "/library/Stat/Final",
    });
  });

  it("does not replace a still-live directory page", () => {
    expect(redirectsFromManifest({
      moves: [{ kind: "move", from: "Causalean.PO.Legacy", to: "Causalean.Stat.Final.Basic" }],
    }, currentModules)).toEqual({});
    expect(redirectsFromManifest({
      moves: [
        { kind: "move", from: "Causalean.PO.Old", to: "Causalean.Stat.Final" },
        { kind: "move", from: "Causalean.PO.Old.Basic", to: "Causalean.Stat.Final.Basic" },
      ],
    }, [...currentModules, "Causalean.PO.Old.Live"])).toEqual({});
  });

  it("rejects cycles instead of emitting redirect loops", () => {
    expect(() => redirectsFromManifest({
      moves: [
        { kind: "move", from: "Causalean.PO.A", to: "Causalean.Stat.B" },
        { kind: "move", from: "Causalean.Stat.B", to: "Causalean.PO.A" },
      ],
    }, currentModules)).toThrow(/Cycle/);
  });

  it("generates and validates an export-portable artifact", () => {
    const directory = mkdtempSync(join(tmpdir(), "library-moves-"));
    try {
      const manifestPath = join(directory, "moves.json");
      const indexPath = join(directory, "library_index.json");
      const artifactPath = join(directory, "library_redirects.json");
      writeFileSync(manifestPath, JSON.stringify(manifest));
      writeFileSync(indexPath, JSON.stringify({ entries: currentModules.map((module) => ({ module })) }));
      generateRedirectArtifact(manifestPath, indexPath, artifactPath);
      expect(loadRedirectArtifact(artifactPath)).toEqual(redirectsFromManifest(manifest, currentModules));
      expect(() => generateRedirectArtifact(manifestPath, indexPath, artifactPath, true)).not.toThrow();
      writeFileSync(artifactPath, "{}\n");
      expect(() => generateRedirectArtifact(manifestPath, indexPath, artifactPath, true)).toThrow(/stale/);
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  });
});
