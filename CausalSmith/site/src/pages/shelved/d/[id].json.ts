import type { APIRoute, GetStaticPaths } from "astro";
import { loadRuns } from "../../../lib/runs.js";

/** One run's long-form record, fetched when its row is opened. */
export const getStaticPaths: GetStaticPaths = () =>
  loadRuns().rows.map((r) => ({ params: { id: r.id } }));

export const GET: APIRoute = ({ params }) =>
  new Response(JSON.stringify(loadRuns().details.get(String(params.id)) ?? null), {
    headers: { "Content-Type": "application/json" },
  });
