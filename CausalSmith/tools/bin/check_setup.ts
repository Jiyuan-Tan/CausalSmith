#!/usr/bin/env node
/**
 * npm run check:setup — warn about machine setup the pipeline depends on but cannot
 * install itself: git's core.longpaths and the configured git-bash (Windows), and
 * the pandoc / latexmk programs `causalsmith present` needs. Warnings only; always
 * exits 0 so it can run on a machine that will never present a paper.
 */
import { setupWarnings } from "../src/shared/setup_checks.js";

const warnings = setupWarnings();
if (warnings.length === 0) {
  console.log("check:setup: OK — no machine-setup warnings");
} else {
  for (const w of warnings) console.warn(`WARN: ${w}`);
  console.warn(`check:setup: ${warnings.length} warning(s)`);
}
