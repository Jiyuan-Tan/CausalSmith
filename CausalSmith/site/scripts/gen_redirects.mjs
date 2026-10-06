import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const siteRoot = dirname(here);
const repoRoot = join(siteRoot, "..", "..");
const defaultManifest = join(repoRoot, "internal", "plans", "module_system", "moves.json");
const defaultIndex = join(repoRoot, "doc", "library_index.json");
const defaultOutput = join(siteRoot, "src", "generated", "library_redirects.json");

function moduleSegments(moduleName) {
  const segments = moduleName.split(".");
  if (segments[0] !== "Causalean" || segments.length < 2 || segments.some((segment) => !segment)) {
    throw new Error(`Expected a Causalean module path, got ${JSON.stringify(moduleName)}`);
  }
  return segments;
}

function pagePath(segments) {
  return `/library/${segments.slice(1).join("/")}`;
}

/**
 * Return the directory-page URL which renders a module. This mirrors
 * `declPagePath` in `src/lib/library.ts`: a leaf module renders in its parent
 * directory, while a module with child modules has a page of its own.
 */
export function modulePagePath(moduleName, moduleNames) {
  const segments = moduleSegments(moduleName);
  const isDirectoryModule = moduleNames.some((candidate) => candidate.startsWith(`${moduleName}.`));
  return pagePath(isDirectoryModule ? segments : segments.slice(0, -1));
}

/** Every directory URL emitted by the library's catch-all static router. */
export function libraryPagePaths(moduleNames) {
  const pages = new Set();
  for (const moduleName of moduleNames) {
    const segments = moduleSegments(moduleName);
    // The area root and each ancestor directory receive a static page.
    for (let end = 2; end < segments.length; end += 1) pages.add(pagePath(segments.slice(0, end)));
    pages.add(modulePagePath(moduleName, moduleNames));
  }
  return pages;
}

function moveMap(manifest) {
  if (!manifest || !Array.isArray(manifest.moves)) {
    throw new Error("moves.json must contain a moves array");
  }
  const moves = new Map();
  for (const move of manifest.moves) {
    if (move.kind !== "move" || typeof move.from !== "string" || typeof move.to !== "string") {
      throw new Error("Each redirect entry must have kind: 'move' and string from/to module paths");
    }
    moduleSegments(move.from);
    moduleSegments(move.to);
    // moves.json is an append-only migration record. A later move can supersede
    // an earlier target for the same old path; the shim in the tree follows the
    // final (last) entry, which is the only redirect destination we should ship.
    moves.set(move.from, move.to);
  }
  return moves;
}

function resolveDestination(start, moves) {
  const seen = new Set();
  let destination = start;
  while (moves.has(destination)) {
    if (seen.has(destination)) {
      throw new Error(`Cycle in moves.json: ${[...seen, destination].join(" -> ")}`);
    }
    seen.add(destination);
    destination = moves.get(destination);
  }
  return destination;
}

function commonPage(paths) {
  const segments = paths.map((path) => path.split("/").filter(Boolean));
  const shared = [];
  for (let i = 0; ; i += 1) {
    const segment = segments[0][i];
    if (segment === undefined || !segments.every((candidate) => candidate[i] === segment)) break;
    shared.push(segment);
  }
  return `/${shared.join("/")}`;
}

/**
 * Build redirects for obsolete library directory pages.
 *
 * A manifest records module paths, whereas the library router emits directory
 * pages. Sources that are still valid pages in the current index are retained;
 * several old files on one removed page are redirected to their closest shared
 * current directory. Every destination is followed through the whole move map.
 */
export function redirectsFromManifest(manifest, currentModules) {
  if (!Array.isArray(currentModules)) throw new Error("library index must supply an array of module names");
  currentModules.forEach(moduleSegments);
  const moves = moveMap(manifest);
  const oldModules = [...moves.keys()];
  const livePages = libraryPagePaths(currentModules);
  const destinationsBySource = new Map();
  const explicitDirectoryDestinations = new Map();

  // Validate every recorded edge, including one whose former page happens to
  // remain live today. Otherwise a future consolidation could hide a cycle.
  oldModules.forEach((sourceModule) => resolveDestination(sourceModule, moves));

  for (const sourceModule of oldModules) {
    const source = modulePagePath(sourceModule, oldModules);
    if (livePages.has(source)) continue;
    const destinationModule = resolveDestination(sourceModule, moves);
    const destination = modulePagePath(destinationModule, currentModules);
    // When the manifest explicitly moves the module which owns this directory
    // page, that edge is more precise than coalescing all descendant moves.
    // A child may legitimately move to another layer without changing where
    // the retired parent page should send readers.
    const ownsSourcePage = oldModules.some((candidate) => candidate.startsWith(`${sourceModule}.`));
    if (ownsSourcePage) {
      if (destination !== source && livePages.has(destination)) {
        explicitDirectoryDestinations.set(source, destination);
      } else {
        // An unusable parent edge must not prevent its children from
        // coalescing to a shared live directory below.
        continue;
      }
    }
    const destinations = destinationsBySource.get(source) ?? new Set();
    destinations.add(destination);
    destinationsBySource.set(source, destinations);
  }

  const redirects = {};
  for (const source of [...destinationsBySource.keys()].sort()) {
    const destination = explicitDirectoryDestinations.get(source)
      ?? commonPage([...destinationsBySource.get(source)].sort());
    if (destination !== source && livePages.has(destination)) redirects[source] = destination;
  }
  return redirects;
}

export function redirectArtifact(manifest, index) {
  if (!index || !Array.isArray(index.entries)) throw new Error("library_index.json must contain an entries array");
  const modules = [...new Set(index.entries.map((entry) => entry.module).filter((moduleName) => typeof moduleName === "string"))].sort();
  return {
    schemaVersion: 1,
    // Deliberately stable: this asset is committed and must not churn on each regeneration.
    redirects: redirectsFromManifest(manifest, modules),
  };
}

/** Load the committed, export-portable redirect asset used by Astro. */
export function loadRedirectArtifact(artifactPath) {
  const artifact = JSON.parse(readFileSync(artifactPath, "utf8"));
  if (!artifact || artifact.schemaVersion !== 1 || !artifact.redirects || typeof artifact.redirects !== "object") {
    throw new Error("library_redirects.json must contain schemaVersion 1 and a redirects object");
  }
  return artifact.redirects;
}

export function generateRedirectArtifact(manifestPath, indexPath, outputPath, check = false) {
  const artifact = redirectArtifact(
    JSON.parse(readFileSync(manifestPath, "utf8")),
    JSON.parse(readFileSync(indexPath, "utf8")),
  );
  const rendered = `${JSON.stringify(artifact, null, 2)}\n`;
  if (check) {
    if (readFileSync(outputPath, "utf8") !== rendered) throw new Error(`${outputPath} is stale; regenerate it`);
  } else {
    mkdirSync(dirname(outputPath), { recursive: true });
    writeFileSync(outputPath, rendered);
  }
  return artifact;
}

function usage() {
  console.log("Usage: node CausalSmith/site/scripts/gen_redirects.mjs [--check] [moves.json library_index.json output.json]");
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const args = process.argv.slice(2);
  if (args[0] === "--help") {
    usage();
  } else {
    const check = args[0] === "--check";
    const paths = check ? args.slice(1) : args;
    if (paths.length !== 0 && paths.length !== 3) throw new Error("Pass either no paths or moves.json, library_index.json, and output.json");
    const [manifestPath, indexPath, outputPath] = paths.length === 3 ? paths : [defaultManifest, defaultIndex, defaultOutput];
    const artifact = generateRedirectArtifact(manifestPath, indexPath, outputPath, check);
    console.log(`${check ? "checked" : "wrote"} ${Object.keys(artifact.redirects).length} library redirects`);
  }
}
