import { afterEach, describe, expect, it, vi } from "vitest";

async function localConfigWith(file: string | null) {
  vi.resetModules();
  vi.doMock("node:fs", async (importOriginal) => {
    const actual = await importOriginal<typeof import("node:fs")>();
    const mockedFs = {
      ...actual,
      existsSync: () => file !== null,
      readFileSync: () => file ?? "",
    };
    return {
      ...mockedFs,
      default: mockedFs,
    };
  });
  return import("../src/local_config.js");
}

const realPlatform = process.platform;
const realGitBashEnv = process.env.CLAUDE_CODE_GIT_BASH_PATH;
function setPlatform(p: NodeJS.Platform) {
  Object.defineProperty(process, "platform", { value: p, configurable: true });
}

afterEach(() => {
  vi.resetModules();
  vi.doUnmock("node:fs");
  setPlatform(realPlatform);
  if (realGitBashEnv === undefined) delete process.env.CLAUDE_CODE_GIT_BASH_PATH;
  else process.env.CLAUDE_CODE_GIT_BASH_PATH = realGitBashEnv;
});

describe("bashBinary", () => {
  const cfg = '{"gitBashPath": "C:/Program Files/Git/bin/bash.exe"}';

  it("prefers CLAUDE_CODE_GIT_BASH_PATH over the file on Windows", async () => {
    process.env.CLAUDE_CODE_GIT_BASH_PATH = "D:/Git/bin/bash.exe";
    setPlatform("win32");
    expect((await localConfigWith(cfg)).bashBinary()).toBe("D:/Git/bin/bash.exe");
  });

  it("spawns the configured git-bash on Windows", async () => {
    delete process.env.CLAUDE_CODE_GIT_BASH_PATH;
    setPlatform("win32");
    expect((await localConfigWith(cfg)).bashBinary()).toBe("C:/Program Files/Git/bin/bash.exe");
  });

  it("falls back to PATH bash on Windows when gitBashPath is unset", async () => {
    delete process.env.CLAUDE_CODE_GIT_BASH_PATH;
    setPlatform("win32");
    expect((await localConfigWith(null)).bashBinary()).toBe("bash");
  });

  it("ignores gitBashPath off Windows", async () => {
    setPlatform("linux");
    expect((await localConfigWith(cfg)).bashBinary()).toBe("bash");
  });
});
