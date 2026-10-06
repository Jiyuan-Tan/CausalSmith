/** Key-order-insensitive JSON: the form to compare two records by CONTENT.
 * `JSON.stringify(a) !== JSON.stringify(b)` reads a payload whose keys arrive in
 * another order as a change; a solver's echo of the node it was shown never
 * has a stable key order. Arrays keep their order (it can be meaningful);
 * `undefined` members are dropped like JSON.stringify does. */
export function stableJson(value: unknown): string {
  if (value === null || typeof value !== "object") return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map((item) => (item === undefined ? "null" : stableJson(item))).join(",")}]`;
  const object = value as Record<string, unknown>;
  return `{${Object.keys(object).filter((key) => object[key] !== undefined).sort().map((key) =>
    `${JSON.stringify(key)}:${stableJson(object[key])}`).join(",")}}`;
}
