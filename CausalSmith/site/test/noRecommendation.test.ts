/**
 * The referee's recommendation (accept / minor_revision / major_revision /
 * reject) is never shown to a reader — user decision, 2026-09-20: show the
 * critique, not the verdict.
 *
 * Three gates, because each one closes a different door:
 *   1. DATA  — the parsed review, for every real bundle and the fixture, does
 *      not carry the word. Nothing a page renders from can contain it.
 *   2. SOURCE — no page, component or library prints the word into markup
 *      (comments stripped, since they never reach the browser).
 *   3. BUILD — when a built site is present, the fixture's paper page and
 *      review page HTML are searched directly. This is the end-to-end check;
 *      it runs after `astro build` and is skipped on a bare test run.
 */
import { describe, expect, it } from "vitest";
import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import { join, resolve } from "node:path";
import { parseReview } from "../src/lib/review.js";

const SITE = resolve(import.meta.dirname, "..");
const PRESENTATION = resolve(SITE, "..", "doc", "presentation");
const FIXTURES = resolve(SITE, "fixtures");

/**
 * The verdict vocabulary. `recommendation` is matched only where it is a FIELD
 * or a LABEL (`"recommendation"`, `Recommendation:`, `<th>Recommendation<`) —
 * one referee writes "a diagnostic recommendation for rounding error" in an
 * ordinary English sentence, and censoring the word itself would be censoring
 * the critique this feature exists to show.
 */
const FORBIDDEN =
  /minor_revision|major_revision|"reject"|recommendation\s*["']?\s*[:<=]|>\s*recommendation\s*</i;

/** Source is ours, so there the bare word is forbidden outright. */
const FORBIDDEN_IN_SOURCE = /minor_revision|major_revision|"reject"|recommendation/i;

function reviewDirs(root: string): string[] {
  if (!existsSync(root)) return [];
  return readdirSync(root)
    .map((n) => join(root, n))
    .filter((d) => existsSync(join(d, "p5_review.json")));
}

describe("1. the parsed review never carries the recommendation", () => {
  const dirs = [...reviewDirs(PRESENTATION), ...reviewDirs(FIXTURES)];

  it("finds reports to check", () => {
    expect(dirs.length).toBeGreaterThan(0);
  });

  for (const dir of dirs) {
    it(`${dir.split("/").pop()}`, () => {
      const raw = JSON.parse(readFileSync(join(dir, "p5_review.json"), "utf8"));
      // The artifact DOES carry it — that is what makes this test meaningful.
      expect(typeof raw.recommendation).toBe("string");
      const review = parseReview(raw);
      expect(JSON.stringify(review)).not.toMatch(FORBIDDEN);
    });
  }
});

// ── 2. nothing in the site source prints it ──────────────────────────────

/** Comments never reach the browser, and this module's own source discusses
 *  the rule at length. Strip them before searching. */
function stripComments(src: string): string {
  return src
    .replace(/\{\s*\/\*[\s\S]*?\*\/\s*\}/g, "") // {/* astro template comment */}
    .replace(/\/\*[\s\S]*?\*\//g, "")
    .replace(/(^|[^:"'`\\])\/\/[^\n]*/g, "$1");
}

function walk(dir: string, out: string[] = []): string[] {
  for (const name of readdirSync(dir)) {
    const p = join(dir, name);
    if (statSync(p).isDirectory()) walk(p, out);
    else if (/\.(astro|ts|css)$/.test(name)) out.push(p);
  }
  return out;
}

describe("2. no page or component prints the recommendation", () => {
  const files = walk(join(SITE, "src"));

  it("scans the whole site source", () => {
    expect(files.length).toBeGreaterThan(20);
  });

  for (const f of files) {
    it(`${f.slice(SITE.length + 1)}`, () => {
      expect(stripComments(readFileSync(f, "utf8"))).not.toMatch(FORBIDDEN_IN_SOURCE);
    });
  }
});

// ── 3. the built HTML, when a build is present ───────────────────────────

/** Every `dist*` directory the repository currently holds. */
const distRoots = readdirSync(SITE)
  .filter((n) => /^dist/.test(n))
  .map((n) => join(SITE, n))
  .filter((d) => statSync(d).isDirectory());

const builtPages = distRoots.flatMap((root) => {
  const papers = join(root, "papers");
  if (!existsSync(papers)) return [] as string[];
  return readdirSync(papers).flatMap((id) =>
    [join(papers, id, "index.html"), join(papers, id, "review", "index.html")].filter((p) =>
      existsSync(p),
    ),
  );
});

describe.runIf(builtPages.length > 0)("3. the built paper and review pages", () => {
  for (const page of builtPages) {
    it(`${page.slice(SITE.length + 1)}`, () => {
      expect(readFileSync(page, "utf8")).not.toMatch(FORBIDDEN);
    });
  }
});
