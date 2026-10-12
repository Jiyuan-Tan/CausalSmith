/**
 * `renderTemplate` substitutes `{{var}}` placeholders, leaving unknown vars
 * intact (so a missing var is visible in the codex output, not silently empty).
 *
 * Replacement uses the function form of `String.replace` so values containing
 * `$1` / `$&` / `$$` are not interpreted as capture references.
 */
export function renderTemplate(tpl: string, vars: Record<string, string>): string {
  return tpl.replace(/{{(\w+)}}/g, (_, k: string) => (k in vars ? vars[k] : `{{${k}}}`));
}
