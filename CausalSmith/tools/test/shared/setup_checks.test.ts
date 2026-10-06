import { describe, expect, it } from "vitest";
import {
  assertPresentationTools,
  gitBashWarning,
  longPathsWarning,
  missingPresentationTools,
  probeProgram,
  setupWarnings,
} from "../../src/shared/setup_checks.js";

const all = () => true;
const without = (absent: string) => (program: string) => program !== absent;

describe("presentation tool preflight", () => {
  it("passes when pandoc and latexmk both launch", () => {
    expect(missingPresentationTools(all)).toEqual([]);
    expect(() => assertPresentationTools(all)).not.toThrow();
  });

  it("names the missing program with an install hint", () => {
    const missing = missingPresentationTools(without("pandoc"));
    expect(missing).toHaveLength(1);
    expect(missing[0]).toMatch(/`pandoc` is missing or does not run/);
    expect(missing[0]).toMatch(/pandoc\.org\/installing/);
    expect(() => assertPresentationTools(without("latexmk"))).toThrow(/`latexmk` is missing or does not run/);
  });
});

describe("probeProgram", () => {
  it("launches a real program and reports an absent one", () => {
    expect(probeProgram(process.execPath)).toBe(true);
    expect(probeProgram("causalsmith-no-such-program-xyz")).toBe(false);
  });
});

describe("Windows setup warnings", () => {
  it("warns about core.longpaths only on Windows and only when not enabled", () => {
    expect(longPathsWarning("linux", () => null)).toBeNull();
    expect(longPathsWarning("win32", () => "true")).toBeNull();
    expect(longPathsWarning("win32", () => "false")).toMatch(/core\.longpaths true/);
    expect(longPathsWarning("win32", () => null)).toMatch(/core\.longpaths true/);
  });

  it("warns when gitBashPath is unset or missing on Windows", () => {
    expect(gitBashWarning("linux", undefined)).toBeNull();
    expect(gitBashWarning("win32", undefined)).toMatch(/gitBashPath is not set/);
    expect(gitBashWarning("win32", "C:/Git/bin/bash.exe", () => false)).toMatch(/does not exist/);
    expect(gitBashWarning("win32", "C:/Git/bin/bash.exe", () => true)).toBeNull();
  });

  it("uses the injected gitBashPath, never this machine's configured one", () => {
    const saved = process.env.CLAUDE_CODE_GIT_BASH_PATH;
    process.env.CLAUDE_CODE_GIT_BASH_PATH = process.execPath; // a real file
    try {
      expect(gitBashWarning("win32", undefined)).toMatch(/gitBashPath is not set/);
      expect(
        setupWarnings({ platform: "win32", probe: all, readGitConfig: () => "true", gitBashPath: undefined }),
      ).toHaveLength(1);
    } finally {
      if (saved === undefined) delete process.env.CLAUDE_CODE_GIT_BASH_PATH;
      else process.env.CLAUDE_CODE_GIT_BASH_PATH = saved;
    }
  });

  it("collects every warning for the host", () => {
    const win = setupWarnings({
      platform: "win32",
      probe: without("pandoc"),
      readGitConfig: () => null,
      gitBashPath: undefined,
    });
    expect(win).toHaveLength(3);
    expect(
      setupWarnings({ platform: "linux", probe: all, readGitConfig: () => null, gitBashPath: undefined }),
    ).toEqual([]);
  });
});
