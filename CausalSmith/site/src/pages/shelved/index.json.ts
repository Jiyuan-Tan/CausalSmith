import type { APIRoute } from "astro";
import { loadRuns } from "../../lib/runs.js";

/** Every shelved run as one compact payload; the list page filters it client-side. */
export const GET: APIRoute = () =>
  new Response(JSON.stringify({ rows: loadRuns().rows }), {
    headers: { "Content-Type": "application/json" },
  });
