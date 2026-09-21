// `release` is the one command that can turn an unpublished paper into a permanent public
// record, so what it is tested for is mostly what it REFUSES to do.
//
//  1. IT STOPS BY DEFAULT. Reserve, restamp, verify, print — and then stop. Publishing takes
//     an explicit `--publish`, because nothing after it can be undone.
//  2. IT PUBLISHES EXACTLY ONCE. Not zero times (a silent no-op is the worst failure a deposit
//     tool has) and never twice.
//  3. SANDBOX SAYS SO AND STOPS. A sandbox DOI is deliberately not stamped — it resolves to
//     nothing — so the stamp check cannot pass and `publish` would refuse. `release` diagnoses
//     that itself instead of letting the operator discover it from a refusal.
//  4. `--dry-run` WRITES NOTHING — not to Zenodo and not to the working tree. The restamp is the
//     one step in this chain that touches the bundle, so it runs in ITS dry-run mode too, and the
//     chain stops right after it rather than checking a stamp on a PDF nobody restamped.
//  5. IT DOES NOT DEADLOCK. reserve, restamp and publish each take the same per-bundle emit
//     lock, which is not re-entrant. This runs the REAL restamp (with only latexmk faked) so
//     the lock acquisition under test is the production one.
//
// Everything runs against a fake `fetch` and a temp bundle: no network, no clock, no TeX.

import { describe, it, expect, beforeEach } from "vitest";
import { createHash } from "node:crypto";
import { mkdir, mkdtemp, readFile, readdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { multiPagePdf, pdfPageTexts } from "./zenodo_fixtures.js";
import { PRODUCTION, SANDBOX, ZenodoClient, type ZenodoEnvironment } from "../src/zenodo/client.js";
import { release } from "../src/zenodo/release.js";
import { restampBundle, type RestampOptions } from "../src/presentation/restamp.js";
import { LatexCompileError } from "../src/presentation/paper_compile.js";
import { reserve, type DepositContext } from "../src/zenodo/deposit.js";
import { SUBCOMMANDS, parseStrict } from "../bin/zenodo_deposit.js";

const TOKEN = "zEn0d0TESTtoken_DO_NOT_LEAK_9f3a2b1c";
const BUNDLE_ID = "stat_demo_release_v1";
const WP_NUMBER = "CSWP-2026-007";
const BODY = ["page two body text", "page three body text"];

let repoRoot: string;
let bundleDir: string;
let calls: { method: string; url: string }[];
let logs: string[];
let warns: string[];

const META = {
  qid: "stat_demo", spec: "release_v1", title: "A demo paper", tldr: "t",
  abstract: "An abstract.", area: "Stat", authorship: null, created: "2026-07-21",
  wp_number: WP_NUMBER, version: 1, revised: "2026-07-21",
  versions: [{ v: 1, date: "2026-07-21", paper_sha256: null }],
  doi: null, version_doi: null, score: 8, score_rationale: "kept",
};

const PAPER_TEX = "\\documentclass{article}\n\\input{paper_macros}\n\\date{\\today}\n\\begin{document}x\\end{document}\n";

beforeEach(async () => {
  calls = [];
  logs = [];
  warns = [];
  repoRoot = path.join(await mkdtemp(path.join(os.tmpdir(), "release-repo-")), "CausalSmith");
  bundleDir = path.join(repoRoot, "doc", "presentation", BUNDLE_ID);
  await mkdir(bundleDir, { recursive: true });
  await writeFile(path.join(bundleDir, "meta.json"), `${JSON.stringify(META, null, 2)}\n`, "utf8");
  await writeFile(path.join(bundleDir, "paper.tex"), PAPER_TEX, "utf8");
  await writeFile(path.join(bundleDir, "paper_macros.tex"), "% stale\n", "utf8");
  await writeFile(path.join(bundleDir, "paper.pdf"), multiPagePdf(["Title page.", ...BODY]));
  await writeFile(
    path.join(repoRoot, "doc", "presentation", "_wp_registry.json"),
    `${JSON.stringify({ [BUNDLE_ID]: WP_NUMBER }, null, 2)}\n`,
    "utf8",
  );
});

/** A fake Zenodo big enough for reserve + publish. Every URL it hands back lives on the
 *  configured instance's own origin — the client refuses to follow a cross-instance link. */
function fakeZenodo(env: ZenodoEnvironment) {
  const prefix = env.name === "production" ? "10.5281" : "10.5072";
  const origin = new URL(env.apiBase).origin;
  const drafts = new Map<number, Record<string, unknown>>();
  let nextId = 100;
  const conceptrecid = 99;
  return async (url: string, init?: RequestInit): Promise<Response> => {
    const method = init?.method ?? "GET";
    const body = typeof init?.body === "string" ? init.body : undefined;
    calls.push({ method, url });
    const json = (status: number, value: unknown) => new Response(JSON.stringify(value), { status });

    if (method === "GET" && url.includes("/deposit/depositions?")) return json(200, []);
    if (method === "POST" && url.endsWith("/deposit/depositions")) {
      const id = nextId++;
      const dep = {
        id, conceptrecid, state: "unsubmitted", submitted: false,
        metadata: { ...(JSON.parse(body ?? "{}").metadata ?? {}) },
        links: { bucket: `${origin}/api/files/bucket-${id}` },
        files: [],
      };
      drafts.set(id, dep);
      return json(201, dep);
    }
    const pub = /\/deposit\/depositions\/(\d+)\/actions\/publish$/.exec(url);
    if (method === "POST" && pub) {
      const id = Number(pub[1]);
      const dep = drafts.get(id) ?? {};
      const done = {
        ...dep, id, conceptrecid, state: "done", submitted: true,
        conceptdoi: `${prefix}/zenodo.${conceptrecid}`, doi: `${prefix}/zenodo.${id}`,
        links: { ...(dep.links as object), record_html: `${origin}/records/${id}` },
      };
      drafts.set(id, done);
      return json(202, done);
    }
    const one = /\/deposit\/depositions\/(\d+)$/.exec(url);
    if (one) {
      const id = Number(one[1]);
      if (method === "GET") {
        const dep = drafts.get(id);
        return dep ? json(200, dep) : json(404, { message: "The persistent identifier does not exist." });
      }
      if (method === "PUT") {
        const next = { ...(drafts.get(id) ?? {}), metadata: JSON.parse(body ?? "{}").metadata };
        drafts.set(id, next);
        return json(200, next);
      }
    }
    if (method === "PUT" && url.includes("/api/files/")) {
      return json(201, { key: "paper.pdf", size: 10, checksum: "md5:fake", version_id: "v1" });
    }
    return json(500, { message: `fake zenodo: unrouted ${method} ${url}` });
  };
}

function ctxFor(env: ZenodoEnvironment, over: Partial<DepositContext> = {}): DepositContext {
  return {
    bundleDir,
    client: new ZenodoClient({
      env,
      tokenProvider: async () => TOKEN,
      fetchImpl: fakeZenodo(env),
      sleep: async () => {},
      maxRetries: 1,
    }),
    writeMeta: env.name === "production",
    allowUnstamped: false,
    siteBaseUrl: "https://causalsmith.org",
    repoUrl: "https://github.com/Jiyuan-Tan/CausalSmith",
    titlePrefix: env.name === "sandbox" ? "[TEST] " : undefined,
    log: (l) => logs.push(l),
    warn: (l) => warns.push(l),
    now: () => new Date("2026-09-21T12:00:00.000Z"),
    ...over,
  };
}

/** A latexmk that draws the generated stamp values on page 1, as the real template does. */
const fakeLatexmk = async (dir: string): Promise<void> => {
  const stamp = await readFile(path.join(dir, "paper_stamp.tex"), "utf8");
  const field = (name: string) =>
    new RegExp(`\\\\renewcommand\\*\\{\\\\${name}\\}\\{([^}]*)\\}`).exec(stamp)?.[1] ?? "";
  const doi = field("csstampdoi");
  await writeFile(
    path.join(dir, "paper.pdf"),
    multiPagePdf([`Title page. ${field("csstampid")}${doi ? ` doi:${doi} ` : " "}[Stat]`, ...BODY]),
  );
};

/** The REAL restamp, with only the compile and the PDF reader injected — so the locking under
 *  test is production locking. */
const restampSeam = (dir: string, o: RestampOptions) =>
  restampBundle(dir, {
    ...o,
    today: "2026-09-21",
    compile: fakeLatexmk,
    readPages: async (p) => ({ pages: pdfPageTexts(await readFile(p)), method: "fixture" }),
    trackedFiles: async () => new Set(["paper.tex", "paper.pdf", "paper_macros.tex", "meta.json"]),
  });

const opts = (over: Partial<Parameters<typeof release>[1]> = {}) => ({
  repoRoot, seriesPrefix: "CSWP", restamp: restampSeam, ...over,
});

const publishCalls = () => calls.filter((c) => c.method === "POST" && c.url.endsWith("/actions/publish"));

/** Every file in the bundle with its hash, minus the lock sentinels a command legitimately makes. */
async function snapshot(): Promise<Record<string, string>> {
  const out: Record<string, string> = {};
  for (const entry of await readdir(bundleDir, { recursive: true, withFileTypes: true })) {
    if (!entry.isFile()) continue;
    const rel = path.relative(bundleDir, path.join(entry.parentPath, entry.name));
    if (/^\.(emit|meta|zenodo)\.lock/.test(rel)) continue;
    out[rel] = createHash("sha256").update(await readFile(path.join(bundleDir, rel))).digest("hex");
  }
  return out;
}

describe("release", () => {
  it("reserves, restamps and STOPS before publishing by default", async () => {
    const result = await release(ctxFor(PRODUCTION), opts());
    expect(result.stoppedBecause).toBe("not-asked");
    expect(result.published).toBeNull();
    expect(publishCalls()).toHaveLength(0);
    // The restamp really happened: page 1 now carries the reserved DOI and the stamp id.
    expect(result.restamped?.verdict).toBe("written");
    const page1 = pdfPageTexts(await readFile(path.join(bundleDir, "paper.pdf")))[0]!;
    expect(page1).toContain("doi:10.5281/zenodo.99");
    expect(page1).toContain("CSWP-2026-007v1");
    // ...and the operator was shown exactly what would be sent.
    const printed = logs.join("\n");
    expect(printed).toContain("WOULD PUBLISH on production");
    expect(printed).toContain("concept DOI  10.5281/zenodo.99");
    expect(printed).toContain("version DOI  10.5281/zenodo.100");
    expect(printed).toContain('"upload_type": "publication"');
  });

  it("does not bump the version while stamping the DOI in", async () => {
    await release(ctxFor(PRODUCTION), opts());
    const meta = JSON.parse(await readFile(path.join(bundleDir, "meta.json"), "utf8"));
    expect(meta.version).toBe(1);
    expect(meta.versions).toHaveLength(1);
    expect(meta.revised).toBe("2026-07-21");
    expect(meta.doi).toBe("10.5281/zenodo.99");
  });

  it("publishes exactly once with --publish", async () => {
    const result = await release(ctxFor(PRODUCTION), opts({ publish: true }));
    expect(result.stoppedBecause).toBeNull();
    expect(result.published?.alreadyPublished).toBe(false);
    expect(result.published?.record.published?.version_doi).toBe("10.5281/zenodo.100");
    expect(publishCalls()).toHaveLength(1);
  });

  it("says why a sandbox release cannot be stamped, and stops even with --publish", async () => {
    const result = await release(ctxFor(SANDBOX), opts({ publish: true }));
    expect(result.stoppedBecause).toBe("sandbox-doi-is-not-stamped");
    expect(publishCalls()).toHaveLength(0);
    expect(warns.join("\n")).toMatch(/STOPPING: 10\.5072\/zenodo\.99 is a SANDBOX DOI/);
    // The containment rule held: the sandbox DOI never reached meta.json, so the stamp had
    // nothing to print and page 1 links to the paper's page instead.
    const meta = JSON.parse(await readFile(path.join(bundleDir, "meta.json"), "utf8"));
    expect(meta.doi).toBeNull();
    expect(pdfPageTexts(await readFile(path.join(bundleDir, "paper.pdf")))[0]).not.toContain("doi:");
  });

  it("lets a sandbox rehearsal through only with --allow-unstamped", async () => {
    const result = await release(ctxFor(SANDBOX, { allowUnstamped: true }), opts({ publish: true }));
    expect(result.stoppedBecause).toBeNull();
    expect(publishCalls()).toHaveLength(1);
  });

  it("stops without publishing when the restamp itself failed", async () => {
    const result = await release(ctxFor(PRODUCTION), opts({
      publish: true,
      // The compile override goes to the REAL restamp, not through `restampSeam` (which would
      // put its own fake latexmk back on top of it).
      restamp: (dir, o) => restampBundle(dir, {
        ...o,
        compile: async () => { throw new LatexCompileError(dir, "! Undefined control sequence."); },
      }),
    }));
    expect(result.stoppedBecause).toBe("restamp-failed");
    expect(publishCalls()).toHaveLength(0);
  });

  it("never deadlocks: reserve, the real restamp and publish all take the same emit lock", async () => {
    // Default vitest timeout is the assertion here — a self-deadlock would sit in the emit
    // lock's bounded retry loop for ten minutes rather than fail fast.
    const result = await release(ctxFor(PRODUCTION), opts({ publish: true }));
    expect(result.restamped?.ok).toBe(true);
    expect(result.published).not.toBeNull();
  });
});

describe("release --dry-run", () => {
  /** Same fake Zenodo, but a client that sends nothing. */
  const dryCtx = () => ctxFor(PRODUCTION, {
    client: new ZenodoClient({
      env: PRODUCTION, tokenProvider: async () => TOKEN, fetchImpl: fakeZenodo(PRODUCTION),
      sleep: async () => {}, maxRetries: 1, dryRun: true,
    }),
  });

  it("writes NOTHING to the bundle — the restamp previews instead of stamping", async () => {
    // The state a dry run is actually used from: the DOI is reserved and recorded, and page 1
    // has never been stamped with it. `release --dry-run` here used to recompile and copy back
    // paper.pdf, paper.tex, paper_stamp.tex and meta.json — permanent changes made by the one
    // command whose entire promise is that it makes none.
    await reserve(ctxFor(PRODUCTION), {});
    const before = await snapshot();

    const result = await release(dryCtx(), opts({ publish: true }));
    expect(result.stoppedBecause).toBe("dry-run");
    expect(result.restamped?.verdict).toBe("would-write");
    expect(result.restamped?.written).toEqual([]);
    expect(result.published).toBeNull();
    expect(publishCalls()).toHaveLength(0);
    expect(await snapshot()).toEqual(before);
    expect(logs.join("\n")).toMatch(/DRY RUN: nothing was written/);
  });

  it("does not print a publish preview built from a PDF it deliberately did not restamp", async () => {
    await reserve(ctxFor(PRODUCTION), {});
    await release(dryCtx(), opts());
    // A stamp verdict here would describe the page 1 that shipped, not the one a real run
    // produces — a confident answer to the wrong question.
    expect(logs.join("\n")).not.toContain("WOULD PUBLISH on");
    expect(logs.join("\n")).not.toContain("page 1 DOI");
  });
});

describe("the release subcommand's argv contract", () => {
  it("is in the strict allowlist and accepts only its own flags", () => {
    expect(SUBCOMMANDS).toContain("release");
    const parsed = parseStrict("release", ["--publish", "--allow-unstamped", "/b"]);
    expect(parsed.bundleDir).toBe("/b");
    expect(parsed.booleans.has("--publish")).toBe(true);
    // `--publish` is release's alone: on the publish subcommand it is a typo, not a no-op.
    expect(() => parseStrict("publish", ["--publish", "/b"])).toThrow(/Unknown flag '--publish'/);
    expect(() => parseStrict("release", ["--repair", "/b"])).toThrow(/Unknown flag '--repair'/);
  });
});
