/** Stable identity of the D-1.2 source revision currently under D0. */
export function proposalRevision(state: {
  proposed_from?: { current_angle_index?: number; current_version?: number };
}): string | undefined {
  const angle = state.proposed_from?.current_angle_index;
  const version = state.proposed_from?.current_version;
  return typeof angle === "number" && typeof version === "number"
    ? `angle:${angle}/version:${version}`
    : undefined;
}
