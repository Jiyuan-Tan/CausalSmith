// The Zenodo client's three load-bearing behaviours, none of which the happy path
// exercises: it must not leak the token, it must survive rate limiting, and it must
// never let a server-supplied link move it between instances.
//
// The token rule is the one worth stating plainly. A personal access token grants
// permanent, irrevocable publishing rights on the user's account; a single copy in a
// CI log, a test snapshot, or a thrown error that gets pasted into an issue is a
// disclosure that cannot be walked back. So redaction is asserted at the boundary —
// on every thrown error and every logged line — rather than trusted to call sites.
//
// The retry rule comes from a measured surprise: the sandbox returns `Retry-After` on
// SUCCESSFUL responses too (it is "seconds left in the rate-limit window", not a
// backoff instruction). A client that honoured it unconditionally would sleep ~60s
// after every 2xx, so the header is read only on a retryable status, and that is
// pinned here.

import { describe, it, expect } from "vitest";
import {
  PRODUCTION,
  SANDBOX,
  ZenodoClient,
  ZenodoError,
  isSandboxDoi,
  redactSecrets,
} from "../src/zenodo/client.js";

const TOKEN = "zEn0d0TESTtoken_DO_NOT_LEAK_9f3a2b1c";

interface Call {
  method: string;
  url: string;
  authorization: string | undefined;
  body: string | undefined;
}

interface Reply {
  status: number;
  body?: unknown;
  text?: string;
  headers?: Record<string, string>;
}

/** A fake `fetch` that replays `replies` in order and records every call. */
function fakeFetch(replies: Reply[]): {
  impl: (url: string, init?: RequestInit) => Promise<Response>;
  calls: Call[];
} {
  const calls: Call[] = [];
  let i = 0;
  const impl = async (url: string, init?: RequestInit): Promise<Response> => {
    const headers = (init?.headers ?? {}) as Record<string, string>;
    calls.push({
      method: init?.method ?? "GET",
      url,
      authorization: headers.Authorization,
      body: typeof init?.body === "string" ? init.body : undefined,
    });
    const reply = replies[Math.min(i, replies.length - 1)];
    i += 1;
    const text = reply.text ?? (reply.body === undefined ? "" : JSON.stringify(reply.body));
    return new Response(text, { status: reply.status, headers: reply.headers });
  };
  return { impl, calls };
}

function client(
  replies: Reply[],
  opts: { sleeps?: number[]; log?: string[]; env?: typeof SANDBOX } = {},
) {
  const { impl, calls } = fakeFetch(replies);
  const sleeps = opts.sleeps ?? [];
  const log = opts.log ?? [];
  const c = new ZenodoClient({
    env: opts.env ?? SANDBOX,
    tokenProvider: async () => TOKEN,
    fetchImpl: impl,
    sleep: async (ms) => void sleeps.push(ms),
    maxRetries: 3,
    backoffBaseMs: 100,
    log: (line) => log.push(line),
  });
  return { c, calls, sleeps, log };
}

describe("redactSecrets", () => {
  it("removes the literal token wherever it appears", () => {
    const out = redactSecrets(`failed with ${TOKEN} in the url`, TOKEN);
    expect(out).not.toContain(TOKEN);
    expect(out).toContain("<REDACTED>");
  });

  it("removes token-shaped material even when the literal is unknown", () => {
    const out = redactSecrets(`Authorization: Bearer ${TOKEN}; access_token=${TOKEN}&x=1`);
    expect(out).not.toContain(TOKEN);
    expect(out).toContain("access_token=<REDACTED>");
    expect(out).toContain("Bearer <REDACTED>");
  });

  it("leaves ordinary text alone", () => {
    expect(redactSecrets("concept DOI 10.5072/zenodo.606199", TOKEN))
      .toBe("concept DOI 10.5072/zenodo.606199");
  });
});

describe("DOI derivation", () => {
  it("composes the concept DOI from the environment prefix, not from prereserve_doi", () => {
    // The sandbox's prereserve_doi claims 10.5281 while it actually mints 10.5072.
    const { c } = client([{ status: 200, body: {} }]);
    expect(c.conceptDoi(606199)).toBe("10.5072/zenodo.606199");
    expect(c.versionDoi(606200)).toBe("10.5072/zenodo.606200");
  });

  it("uses the production prefix on the production instance", () => {
    const { c } = client([{ status: 200, body: {} }], { env: PRODUCTION });
    expect(c.conceptDoi(999)).toBe("10.5281/zenodo.999");
  });

  it("recognises a sandbox DOI so it can be kept out of meta.json", () => {
    expect(isSandboxDoi("10.5072/zenodo.606199")).toBe(true);
    expect(isSandboxDoi("10.5281/zenodo.606199")).toBe(false);
    expect(isSandboxDoi(null)).toBe(false);
  });
});

describe("token handling", () => {
  it("sends the token as a bearer header and never in the URL", async () => {
    const { c, calls } = client([{ status: 201, body: { id: 1, conceptrecid: 2, links: { bucket: "https://sandbox.zenodo.org/api/files/b" } } }]);
    await c.createDraft();
    expect(calls[0].authorization).toBe(`Bearer ${TOKEN}`);
    expect(calls[0].url).not.toContain(TOKEN);
  });

  it("keeps the token out of a thrown error, even when Zenodo echoes it back", async () => {
    const { c } = client([
      { status: 400, body: { message: `Bad request for access_token=${TOKEN}`, errors: [{ field: "metadata.title", messages: ["is required"] }] } },
    ]);
    const err = await c.createDraft().then(() => null, (e: unknown) => e);
    expect(err).toBeInstanceOf(ZenodoError);
    const zerr = err as ZenodoError;
    expect(zerr.status).toBe(400);
    expect(zerr.message).not.toContain(TOKEN);
    expect(JSON.stringify(zerr)).not.toContain(TOKEN);
    expect(zerr.message).toContain("metadata.title: is required");
  });

  it("keeps the token out of an error whose body is not JSON", async () => {
    const { c } = client([{ status: 502, text: `<html>proxy error ${TOKEN}</html>` }]);
    const err = await c
      .getDeposition(5)
      .then(() => null, (e: unknown) => (e instanceof Error ? e.message : String(e)));
    expect(String(err)).not.toContain(TOKEN);
  });

  it("keeps the token out of an error raised before any response", async () => {
    const boom = async (): Promise<Response> => {
      throw new Error(`socket hang up while sending Bearer ${TOKEN}`);
    };
    const c = new ZenodoClient({
      env: SANDBOX,
      tokenProvider: async () => TOKEN,
      fetchImpl: boom,
      sleep: async () => {},
      maxRetries: 0,
    });
    const msg = await c.getDeposition(1).then(() => "", (e: unknown) => (e as Error).message);
    expect(msg).not.toContain(TOKEN);
    expect(msg).toContain("<REDACTED>");
  });

  it("keeps the token out of the request log and the dry-run transcript", async () => {
    const log: string[] = [];
    // A GET, because a POST is no longer replayed after 429 (audit r2).
    const { c } = client([{ status: 429, headers: { "retry-after": "1" } }, { status: 200, body: { id: 7, conceptrecid: 6, links: {} } }], { log });
    await c.getDeposition(7);
    expect(log.length).toBeGreaterThan(0);
    expect(log.join("\n")).not.toContain(TOKEN);
    expect(c.requestLog.join("\n")).not.toContain(TOKEN);
  });
});

describe("retry and backoff", () => {
  it("honours Retry-After on a 429 for an idempotent request", async () => {
    const sleeps: number[] = [];
    const { c, calls } = client(
      [{ status: 429, headers: { "retry-after": "2" } }, { status: 200, body: { id: 1, conceptrecid: 2 } }],
      { sleeps },
    );
    expect((await c.getDeposition(1)).id).toBe(1);
    expect(calls).toHaveLength(2);
    expect(sleeps).toEqual([2000]);
  });

  it("does NOT sleep on a Retry-After returned with a successful response", async () => {
    // The sandbox sends `retry-after: 59` alongside 2xx; treating that as a backoff
    // instruction would stall every successful call for a minute.
    const sleeps: number[] = [];
    const { c } = client([{
      status: 201, headers: { "retry-after": "59" },
      body: { id: 1, conceptrecid: 2, links: { bucket: "https://sandbox.zenodo.org/api/files/b" } },
    }], { sleeps });
    await c.createDraft();
    expect(sleeps).toEqual([]);
  });

  it("backs off exponentially with jitter on 5xx (idempotent request)", async () => {
    const sleeps: number[] = [];
    const { c, calls } = client(
      [{ status: 500 }, { status: 503 }, { status: 200, body: { id: 3, conceptrecid: 2 } }],
      { sleeps },
    );
    await c.getDeposition(3);
    expect(calls).toHaveLength(3);
    expect(sleeps).toHaveLength(2);
    // base 100ms: ceilings are 100 and 200, with full jitter in [ceiling/2, ceiling].
    expect(sleeps[0]).toBeGreaterThanOrEqual(50);
    expect(sleeps[0]).toBeLessThanOrEqual(100);
    expect(sleeps[1]).toBeGreaterThanOrEqual(100);
    expect(sleeps[1]).toBeLessThanOrEqual(200);
  });

  it("gives up after maxRetries and surfaces the last status", async () => {
    const sleeps: number[] = [];
    const { c, calls } = client([{ status: 503, body: { message: "upstream down" } }], { sleeps });
    const err = await c.getDeposition(1).then(() => null, (e: unknown) => e as ZenodoError);
    expect(calls).toHaveLength(4); // 1 attempt + 3 retries
    expect(err?.status).toBe(503);
    expect(err?.zenodoMessage).toBe("upstream down");
  });

  it("does not retry a 4xx that is not 429", async () => {
    const { c, calls } = client([{ status: 403, body: { message: "forbidden" } }]);
    await c.publish(1).catch(() => {});
    expect(calls).toHaveLength(1);
  });

  it("does not retry a non-idempotent POST after a 5xx — see zenodo_audit_r1", async () => {
    // Replaying a create/publish/newversion can duplicate a permanent record, so an
    // ambiguous outcome is surfaced rather than retried. The earlier version of this
    // suite asserted the opposite and so codified the unsafe policy.
    const { c, calls } = client([{ status: 503, body: { message: "upstream" } }]);
    await c.createDraft().catch(() => {});
    expect(calls).toHaveLength(1);
  });

  it("caps a hostile Retry-After at maxSleepMs", async () => {
    const sleeps: number[] = [];
    const { impl } = fakeFetch([{ status: 429, headers: { "retry-after": "86400" } }, { status: 200, body: { id: 1 } }]);
    const c = new ZenodoClient({
      env: SANDBOX,
      tokenProvider: async () => TOKEN,
      fetchImpl: impl,
      sleep: async (ms) => void sleeps.push(ms),
      maxRetries: 2,
      maxSleepMs: 5_000,
    });
    await c.getDeposition(1);
    expect(sleeps).toEqual([5_000]);
  });

  it("retries a network-level failure on an idempotent request", async () => {
    const sleeps: number[] = [];
    let n = 0;
    const impl = async (): Promise<Response> => {
      n += 1;
      if (n === 1) throw new Error("ECONNRESET");
      return new Response(JSON.stringify({ id: 9, conceptrecid: 8 }), { status: 200 });
    };
    const c = new ZenodoClient({
      env: SANDBOX,
      tokenProvider: async () => TOKEN,
      fetchImpl: impl,
      sleep: async (ms) => void sleeps.push(ms),
      maxRetries: 2,
      backoffBaseMs: 10,
    });
    expect((await c.getDeposition(9)).id).toBe(9);
    expect(sleeps).toHaveLength(1);
  });
});

describe("instance containment", () => {
  it("refuses to follow a link that points at the other instance", async () => {
    const { c } = client([
      { status: 201, body: { id: 1, links: { latest_draft: "https://zenodo.org/api/deposit/depositions/999" } } },
    ]);
    const msg = await c.newVersion(1).then(() => "", (e: unknown) => (e as Error).message);
    expect(msg).toContain("Refusing to follow");
    expect(msg).toContain("https://zenodo.org");
  });

  it("fails loudly when newversion returns no latest_draft rather than guessing an id", async () => {
    const { c } = client([{ status: 201, body: { id: 1, links: {} } }]);
    const msg = await c.newVersion(1).then(() => "", (e: unknown) => (e as Error).message);
    expect(msg).toContain("no links.latest_draft");
  });
});

describe("operations", () => {
  it("treats a 404 as 'no such deposition' rather than an error", async () => {
    const { c } = client([{ status: 404, body: { message: "The persistent identifier does not exist." } }]);
    expect(await c.getDepositionOrNull(606202)).toBeNull();
  });

  it("uploads through the bucket API, which replaces an existing key in place", async () => {
    const { c, calls } = client([{ status: 201, body: { key: "paper.pdf", size: 4, checksum: "md5:x" } }]);
    const out = await c.uploadFile("https://sandbox.zenodo.org/api/files/abc", "paper.pdf", new Uint8Array([1, 2, 3, 4]));
    expect(calls[0].method).toBe("PUT");
    expect(calls[0].url).toBe("https://sandbox.zenodo.org/api/files/abc/paper.pdf");
    expect(out.key).toBe("paper.pdf");
  });

  it("follows links.latest_draft to the new draft on newVersion", async () => {
    const { c, calls } = client([
      { status: 201, body: { id: 1, links: { latest_draft: "https://sandbox.zenodo.org/api/deposit/depositions/606203" } } },
      { status: 200, body: { id: 606203, conceptrecid: 606199, conceptdoi: "10.5072/zenodo.606199", state: "unsubmitted" } },
    ]);
    const draft = await c.newVersion(606200);
    expect(draft.id).toBe(606203);
    expect(draft.conceptrecid).toBe(606199);
    expect(calls[1].method).toBe("GET");
  });

  it("sends nothing that mutates under dryRun, but still records the request", async () => {
    const { impl, calls } = fakeFetch([{ status: 201, body: { id: 1 } }]);
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, dryRun: true });
    await c.createDraft();
    await c.publish(1);
    await c.deleteDraft(1);
    expect(calls).toHaveLength(0);
    expect(c.requestLog).toHaveLength(3);
    expect(c.requestLog[0]).toContain("POST https://sandbox.zenodo.org/api/deposit/depositions");
  });

  it("does NOT stub a malformed success outside dry-run", async () => {
    const { impl } = fakeFetch([{ status: 201, text: "not json" }]);
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl });
    await expect(c.createDraft()).rejects.toThrow(/valid JSON/i);
  });
});
