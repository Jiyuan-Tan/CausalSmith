/**
 * Calendar-date handling for the published paper record.
 *
 * Every date the bundle contract carries — `created`, `revised`, each `versions[].date` — ends up
 * printed on a PDF, in a citation, and in a DOI deposit. So "looks like a date" is not good
 * enough: `2026-02-31` passes a regexp and then prints as "31 February 2026", and `2025-1-01`
 * passes nothing but used to be silently replaced with today, which moves a paper into the wrong
 * year and therefore gives it the wrong working-paper number.
 *
 * Everything here works off the STRING, and where a `Date` is needed it is pinned to UTC. A
 * `new Date("2026-01-01")` is midnight UTC but `toLocaleDateString`/`getFullYear` read it back in
 * the host's zone, so west of UTC a 1 January paper reports as the previous year. None of that
 * may reach a published record.
 */

/** `YYYY-MM-DD` that also names a date that exists (round-trips through UTC). */
export function isCalendarIsoDate(value: unknown): value is string {
  if (typeof value !== "string" || !/^\d{4}-\d{2}-\d{2}$/.test(value)) return false;
  const parsed = new Date(`${value}T00:00:00.000Z`);
  return !Number.isNaN(parsed.getTime()) && parsed.toISOString().slice(0, 10) === value;
}

/** `value` as a calendar date, or a loud failure naming what was wrong and where it came from. */
export function assertCalendarIsoDate(label: string, value: unknown): string {
  if (!isCalendarIsoDate(value)) {
    throw new Error(
      `${label}: ${JSON.stringify(value)} is not a real calendar date in YYYY-MM-DD form. ` +
        "Dates in a bundle's meta.json are published as the paper's own record — correct it by hand " +
        "rather than letting the pipeline guess.",
    );
  }
  return value;
}

/** Year of a calendar ISO date, read off the string so no timezone can shift it. */
export function isoYear(iso: string): number {
  return Number(assertCalendarIsoDate("invalid ISO date", iso).slice(0, 4));
}

/** Today in UTC as `YYYY-MM-DD`. `toISOString` is UTC by construction, so an emit just before
 *  midnight cannot be stamped with the operator's local calendar day. */
export function utcToday(now: Date = new Date()): string {
  return now.toISOString().slice(0, 10);
}

/** Split a validated calendar date for formatting. */
export function isoParts(iso: string): { y: string; m: number; d: number } {
  const value = assertCalendarIsoDate("invalid ISO date", iso);
  return { y: value.slice(0, 4), m: Number(value.slice(5, 7)), d: Number(value.slice(8, 10)) };
}
