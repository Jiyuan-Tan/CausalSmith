import { describe, expect, it } from "vitest";
import { resolveCodexSandboxMode, effectiveSandboxMode } from "../src/shared/codex.js";

describe("resolveCodexSandboxMode", () => {
  it("keeps workspace-write as the portable default", () => {
    expect(resolveCodexSandboxMode({ env: {} })).toBe("workspace-write");
  });

  it("honors an explicit local-config opt-in", () => {
    expect(
      resolveCodexSandboxMode({ env: {}, configured: "danger-full-access" }),
    ).toBe("danger-full-access");
  });

  it("lets the environment override local configuration", () => {
    expect(
      resolveCodexSandboxMode({
        env: { CAUSALSMITH_CODEX_SANDBOX: "workspace-write" },
        configured: "danger-full-access",
      }),
    ).toBe("workspace-write");
  });

  it("fails closed on an invalid override", () => {
    expect(() =>
      resolveCodexSandboxMode({
        env: { CAUSALSMITH_CODEX_SANDBOX: "read-only" },
      }),
    ).toThrow(/must be workspace-write or danger-full-access/);
  });
});

describe("effectiveSandboxMode (per-call narrowing)", () => {
  it("honours a narrowing under workspace-write, and never replaces a configured danger-full-access", () => {
    expect(effectiveSandboxMode(undefined, "workspace-write")).toBe("workspace-write");
    expect(effectiveSandboxMode("read-only", "workspace-write")).toBe("read-only");
    expect(effectiveSandboxMode("workspace-write", "workspace-write")).toBe("workspace-write");
    // danger-full-access in the config means Codex's sandbox cannot start on this host: every
    // call uses it, whatever the call asked for.
    expect(effectiveSandboxMode(undefined, "danger-full-access")).toBe("danger-full-access");
    expect(effectiveSandboxMode("read-only", "danger-full-access")).toBe("danger-full-access");
    expect(effectiveSandboxMode("workspace-write", "danger-full-access")).toBe("danger-full-access");
  });
});
