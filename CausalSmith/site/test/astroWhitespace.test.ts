import { describe, expect, it } from "vitest";
import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import { join, resolve } from "node:path";

/**
 * Astro drops the whitespace BETWEEN two adjacent `{…}` expressions.
 *
 * `v{m.version} {formatDate(m.revised)}` looks like it renders "v3 27 Aug
 * 2026" and renders "v327 Aug 2026" — which is what the live landing page
 * said for three rounds, because no test looked at the text between the two
 * values (audit r4).
 *
 * There is no way to write that safely, so the pattern is simply banned: build
 * the string in the frontmatter and render one expression.
 */

const SITE = resolve(import.meta.dirname, "..");
const COMPONENTS = [join(SITE, "src", "components"), join(SITE, "src", "pages")];

function astroFiles(dir: string, out: string[] = []): string[] {
  if (!existsSync(dir)) return out;
  for (const name of readdirSync(dir)) {
    const p = join(dir, name);
    if (statSync(p).isDirectory()) astroFiles(p, out);
    else if (name.endsWith(".astro")) out.push(p);
  }
  return out;
}

/** The template half of an .astro file — the frontmatter is ordinary TS. */
function template(src: string): string {
  const end = src.indexOf("\n---", 3);
  return src.startsWith("---") && end >= 0 ? src.slice(end + 4) : src;
}

/**
 * Blanks out every tag, keeping the file's length and line breaks.
 * An attribute position — `foo={…} bar={…}` inside a tag — is not an
 * adjacency, so the braces in there must not be seen at all.
 */
function maskTags(tpl: string): string {
  return tpl.replace(/<[^>\n]*>/g, (t) => " ".repeat(t.length));
}

/** `{` → matching `}` over already-masked text; unbalanced braces are dropped. */
function bracePairs(masked: string): Map<number, number> {
  const pairs = new Map<number, number>();
  const stack: number[] = [];
  for (let i = 0; i < masked.length; i++) {
    if (masked[i] === "{") stack.push(i);
    else if (masked[i] === "}") {
      const open = stack.pop();
      if (open !== undefined) pairs.set(open, i);
    }
  }
  return pairs;
}

/**
 * Is this the body of an expression that renders a VALUE?
 *
 * `{m.version}` and `{formatDate(m.revised)}` are values, and two of them with
 * only whitespace between is the bug. `{cond && <>…</>}` is a block that wraps
 * markup — its braces are structure, and two such blocks one under the other
 * is how every .astro file in the tree is written.
 */
function isValueExpression(body: string): boolean {
  return body.trim().length > 0 && !/[<>]|&&|\|\||=>|\?|\/[*/]|\breturn\b/.test(body);
}

/**
 * `{" "}` and `{" · "}` are string literals: their own spaces are inside the
 * value and survive. Writing one is the documented REMEDY for this bug, so an
 * adjacency that involves one is deliberate, not an instance of it.
 */
function isLiteralText(body: string): boolean {
  return /^\s*(['"])(?:[^'"\\]|\\.)*\1\s*$/.test(body);
}

/**
 * Finds `}` … whitespace … `{` where BOTH sides are value expressions.
 *
 * The gap may cross NEWLINES: Astro drops that whitespace too, so a detector
 * that only looked within one line could be walked past by reformatting the
 * very line it was written for. `matchAll` rather than `exec`, so a line that
 * does it twice reports twice.
 */
function adjacentExpressions(tpl: string): string[] {
  const masked = maskTags(tpl);
  const pairs = bracePairs(masked);
  const closers = new Map([...pairs].map(([open, close]) => [close, open]));
  const hits: string[] = [];
  for (const m of masked.matchAll(/\}\s*\{/g)) {
    const closeAt = m.index!;
    const openAt = closeAt + m[0].length - 1;
    const leftOpen = closers.get(closeAt);
    const rightClose = pairs.get(openAt);
    if (leftOpen === undefined || rightClose === undefined) continue;
    // The gap has to be whitespace in the SOURCE as well: masking a tag left
    // spaces behind, and `<span>{a}</span> <span>{b}</span>` is markup between
    // two expressions, not two expressions against each other.
    if (!/^\s*$/.test(tpl.slice(closeAt + 1, openAt))) continue;
    const left = masked.slice(leftOpen + 1, closeAt);
    const right = masked.slice(openAt + 1, rightClose);
    if (isLiteralText(left) || isLiteralText(right)) continue;
    if (!isValueExpression(left) || !isValueExpression(right)) continue;
    // Report from the SOURCE, which still has the markup the mask removed.
    const start = tpl.lastIndexOf("\n", leftOpen) + 1;
    const end = tpl.indexOf("\n", rightClose);
    hits.push(tpl.slice(start, end < 0 ? tpl.length : end).trim());
  }
  return hits;
}

describe("the detector itself", () => {
  // A lint that cannot see the bug it was written for is furniture.
  it("catches the line that shipped the bug", () => {
    const shipped = "      {showRevision && <> &middot; v{m.version} {formatDate(m.revised)}</>}";
    expect(adjacentExpressions(shipped)).toHaveLength(1);
  });

  it("does not flag attributes or a block that merely wraps markup", () => {
    expect(adjacentExpressions('  <a href={href} set:html={renderTexLine(t)} />')).toEqual([]);
    expect(adjacentExpressions("  {a && <span>x</span>}")).toEqual([]);
    expect(adjacentExpressions("  {x} literal {y}")).toEqual([]);
    // Two conditional blocks stacked is the ordinary way to write a page.
    expect(adjacentExpressions("  {a && <b>x</b>}\n  {c && <b>y</b>}")).toEqual([]);
    // …and `{" "}` is the remedy for this bug, so it is never an instance.
    expect(adjacentExpressions('  {note(x)}\n  {" "}Produced by a referee')).toEqual([]);
    expect(adjacentExpressions('  v{m.version} {" "} {formatDate(m.revised)}')).toEqual([]);
  });

  // Reformatting the shipped line onto two lines does not make it correct, so
  // it must not make the detector blind either.
  it("sees across a newline, and reports every hit on a line", () => {
    expect(adjacentExpressions("  v{m.version}\n  {formatDate(m.revised)}")).toHaveLength(1);
    expect(adjacentExpressions("  {a} {b} {c}")).toHaveLength(2);
  });
});

describe("no two adjacent expressions separated only by whitespace", () => {
  const files = COMPONENTS.flatMap((d) => astroFiles(d));

  it("scans the site's components and pages", () => {
    expect(files.length).toBeGreaterThan(5);
  });

  for (const f of files) {
    it(`${f.slice(SITE.length + 1)}`, () => {
      const hits = adjacentExpressions(template(readFileSync(f, "utf8")));
      expect(
        hits,
        `Astro drops the space between these expressions — build one string in the frontmatter:\n  ${hits.join("\n  ")}`,
      ).toEqual([]);
    });
  }
});

// ── the same thing, measured on the built page ──────────────────────────

/** Every `dist*` the repository currently holds. */
const dists = readdirSync(SITE)
  .filter((n) => /^dist/.test(n))
  .map((n) => join(SITE, n))
  .filter((d) => statSync(d).isDirectory() && existsSync(join(d, "index.html")));

/**
 * A measurement that silently does not run is worse than one that fails: for
 * three rounds the landing page said "v327 Aug 2026" and every suite was
 * green. `describe.runIf(false)` registers NOTHING, so the absence of the
 * built-page check looked exactly like a pass.
 *
 * So the block always registers. With no `dist*` to read it reports itself —
 * as a hard failure when the caller asked for the measurement
 * (`SITE_REQUIRE_DIST=1`, which the release build sets after `astro build`),
 * and otherwise as ONE explicit skip that names the reason, so a plain
 * `npx vitest run` in a clean checkout stays green and still says out loud
 * that the built page was not looked at. `SITE_ALLOW_NO_DIST=1` forces the
 * skip even in require mode.
 */
const NO_DIST_IS_FATAL =
  process.env.SITE_REQUIRE_DIST === "1" && process.env.SITE_ALLOW_NO_DIST !== "1";

const NO_DIST_REASON =
  "no dist* directory to measure: run `astro build` first " +
  "(set SITE_REQUIRE_DIST=1 to make this absence a failure)";

describe("the built landing row", () => {
  if (dists.length === 0) {
    if (NO_DIST_IS_FATAL) {
      it("has a built site to measure", () => {
        throw new Error(
          "SITE_REQUIRE_DIST=1 but there is no dist*/index.html to read. " +
            "Build the site, or set SITE_ALLOW_NO_DIST=1 to allow the skip.",
        );
      });
    } else {
      it.skip(NO_DIST_REASON, () => {});
    }
  }
  for (const dist of dists) {
    it(`${dist.slice(SITE.length + 1)} keeps the space inside the revision label`, () => {
      const html = readFileSync(join(dist, "index.html"), "utf8");
      const rows = [...html.matchAll(/<span class="wp-id">([\s\S]*?)<\/span>/g)].map((m) =>
        m[1].replace(/<[^>]+>/g, "").replace(/&middot;/g, "\u00b7").replace(/\s+/g, " ").trim(),
      );
      expect(rows.length).toBeGreaterThan(0);
      for (const row of rows) {
        // "v3 27 Aug 2026", never "v327 Aug 2026".
        expect(row, row).not.toMatch(/v\d+\d{1,2} [A-Z][a-z]{2} \d{4}/);
        const m = /\bv(\d+) (\d{1,2} [A-Z][a-z]{2} \d{4})/.exec(row);
        if (row.includes("\u00b7 v")) expect(m, row).not.toBeNull();
      }
      // The fixture row states it exactly.
      if (html.includes("demo_paper_v1")) {
        expect(rows.some((r) => r.includes("v3 27 Aug 2026")), rows.join(" | ")).toBe(true);
      }
    });
  }
});
