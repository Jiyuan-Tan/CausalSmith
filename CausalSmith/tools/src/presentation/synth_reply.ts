/**
 * The definition writer's reply. LaTeX inside a JSON string is a trap: `\ne`, `\tau`, `\rho`,
 * `\beta`, `\frac` all begin with a JSON escape, so an unescaped backslash decodes to a control
 * character and the body reaches the paper mangled (`\ne` → newline + `e`, observed live). The
 * writer therefore returns delimited blocks, the same shape the render loop uses; a JSON array is
 * still accepted from a reply that ignored the format.
 */
import { parseJsonArrayLoose } from "./gates.js";

export interface SynthReplyGroup { symbols: string[]; title?: string; body: string }

const BLOCK = /@@@DEF@@@\s*\n([\s\S]*?)@@@BODY@@@\s*\n([\s\S]*?)\n?@@@END@@@/g;

export function parseSynthReply(stdout: string): SynthReplyGroup[] | null {
  const groups: SynthReplyGroup[] = [];
  for (const m of stdout.matchAll(BLOCK)) {
    const head = m[1];
    const symbols = (head.match(/^SYMBOLS:\s*(.*)$/m)?.[1] ?? "").split(";").map((s) => s.trim()).filter(Boolean);
    const title = head.match(/^TITLE:\s*(.*)$/m)?.[1]?.trim() || undefined;
    groups.push({ symbols, title, body: m[2].trim() });
  }
  // A sentinel inside a body ends the block early and leaves a stray sentinel between blocks:
  // treat such a reply as unparseable rather than ship a cut definition.
  if (groups.length > 0 && stdout.replace(BLOCK, "").includes("@@@")) return null;
  if (groups.length > 0) return groups;
  const parsed = parseJsonArrayLoose(stdout);
  if (Array.isArray(parsed) && parsed.every((g) => g !== null && typeof g === "object" && !Array.isArray(g))) {
    return (parsed as Partial<SynthReplyGroup>[]).map((g) => ({ symbols: g.symbols ?? [], title: g.title, body: g.body ?? "" }));
  }
  return null;
}
