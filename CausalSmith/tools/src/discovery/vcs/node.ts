// The versioned theorem graph: node model.
//
// One immutable JSON blob per node. A blob is self-describing (`node_type` + `body`)
// and content-addressed by `blobId` = sha256 of its key-order-insensitive JSON, so
// two blobs with the same id are byte-equivalent by construction and a blob read
// back can be verified against its name.
//
// Two identities, two purposes, ONE function each:
//   • `blobId`     — storage identity. Any byte of the node (prose, edges, proof,
//                    layout) changes it. Used by trees and diffs.
//   • `contentKey` — mathematical identity. Only the fields a PROOF rests on
//                    (the claim / construction / condition / symbol meaning, with
//                    TeX whitespace canonicalized) change it. Used by proof bases.
// A TeX re-flow of a claim therefore yields a new blob (the file changed) but the
// same content key (no proof written against it goes stale).
import { createHash } from "node:crypto";
import type { CoreAssumption, CoreDefinition, CoreStatement, CoreSymbol } from "../core/schema.js";
import { stableJson } from "../../shared/stable_json.js";
import { canonicalClaimText } from "../../shared/tex_text.js";

export type NodeId = string;

export type NodeType = "meta" | "symbol" | "assumption" | "definition" | "statement" | "bib";

/** A statement as stored: `status` is DERIVED (never stored), `proof_basis` records the
 *  content keys the proof was written against, `resolved_by` tombstones an answered
 *  open question (the node stays addressable; the render omits it). */
export type StatementBody = Omit<CoreStatement, "status"> & {
  proof_basis?: Record<NodeId, string>;
  resolved_by?: string;
};
/** `used_by` is derived at render time. */
export type AssumptionBody = Omit<CoreAssumption, "used_by">;
export type DefinitionBody = CoreDefinition;
export type SymbolBody = CoreSymbol;
export interface BibBody { key: string; citation?: string }
/** Top-level core fields that are not nodes (target, prose, comparator table …). */
export type MetaBody = Record<string, unknown>;

export type NodeBlob =
  | { node_type: "meta"; body: MetaBody }
  | { node_type: "symbol"; body: SymbolBody }
  | { node_type: "assumption"; body: AssumptionBody }
  | { node_type: "definition"; body: DefinitionBody }
  | { node_type: "statement"; body: StatementBody }
  | { node_type: "bib"; body: BibBody };

export const META_ID: NodeId = "meta";
export const STATEMENT_PREFIX = /^(thm|lem|prop|oeq|conj):/;

export function symbolNodeId(name: string): NodeId {
  return `sym:${name}`;
}
export function bibNodeId(key: string): NodeId {
  return `bib:${key}`;
}

/** The node type an id denotes, or null for an id outside the grammar. */
export function nodeTypeOf(id: NodeId): NodeType | null {
  if (id === META_ID) return "meta";
  if (id.startsWith("sym:")) return "symbol";
  if (id.startsWith("bib:")) return "bib";
  if (id.startsWith("ass:")) return "assumption";
  if (id.startsWith("def:")) return "definition";
  if (STATEMENT_PREFIX.test(id)) return "statement";
  return null;
}

export function sha256Hex(text: string): string {
  return createHash("sha256").update(text, "utf8").digest("hex");
}

/** Storage identity: sha256 over the key-order-insensitive JSON of the whole blob. */
export function blobId(blob: NodeBlob): string {
  return sha256Hex(stableJson(blob));
}

const canon = (value: string | undefined): string | undefined =>
  value === undefined ? undefined : canonicalClaimText(value);

/** Mathematical identity: the fields a proof's soundness rests on. Layout, prose,
 *  edges, proof text, provenance tags and bibliography never enter. */
export function contentKey(blob: NodeBlob): string {
  switch (blob.node_type) {
    case "statement":
      return sha256Hex(stableJson({
        t: "statement",
        kind: blob.body.kind,
        claim: canon(blob.body.statement),
      }));
    case "definition":
      return sha256Hex(stableJson({
        t: "definition",
        name: blob.body.name,
        construction: canon(blob.body.construction),
        inputs: blob.body.inputs,
        by_member_properties: blob.body.by_member_properties,
      }));
    case "assumption":
      return sha256Hex(stableJson({
        t: "assumption",
        condition: canon(blob.body.condition),
        constants: blob.body.constants,
      }));
    case "symbol":
      // Same field set as the retired `symbolBasis`: everything but `refs` (which
      // is a dependency declaration, not meaning).
      return sha256Hex(stableJson({
        t: "symbol",
        name: blob.body.name,
        type: canon(blob.body.type),
        space: canon(blob.body.space),
        sig: canon(blob.body.sig),
        def: canon(blob.body.def),
        role: blob.body.role,
        ref: blob.body.ref,
      }));
    case "bib":
      return sha256Hex(stableJson({ t: "bib", key: blob.body.key, citation: blob.body.citation }));
    case "meta":
      return sha256Hex(stableJson({ t: "meta", body: blob.body }));
  }
}

/** Does the blob's declared type agree with the id it is filed under? */
export function blobMatchesId(id: NodeId, blob: NodeBlob): boolean {
  const expected = nodeTypeOf(id);
  if (expected === null || expected !== blob.node_type) return false;
  switch (blob.node_type) {
    case "symbol": return symbolNodeId(blob.body.name) === id;
    case "bib": return bibNodeId(blob.body.key) === id;
    case "meta": return id === META_ID;
    default: return blob.body.id === id;
  }
}

/** Minimal shape validation of a parsed blob before it is trusted as a `NodeBlob`. */
export function isNodeBlob(value: unknown): value is NodeBlob {
  if (value === null || typeof value !== "object") return false;
  const v = value as { node_type?: unknown; body?: unknown };
  const types: NodeType[] = ["meta", "symbol", "assumption", "definition", "statement", "bib"];
  return types.includes(v.node_type as NodeType) && v.body !== null && typeof v.body === "object";
}
