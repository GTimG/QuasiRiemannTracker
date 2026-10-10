import { cmp, fraction, rational, sub } from "./rational.mjs";

// Catalogue evidence is separate from the signed Comparator/NanoDa registry.
export const contributionDate = (r) => r.timeline_at || r.first_verified_at;
export const historicalBaseline = (r) => r.status === "historical-baseline";
export const formatContributionDate = (r) =>
  new Date(contributionDate(r)).toLocaleDateString("en-GB", {
    ...(r.date_precision === "year" ? {} : { day: "2-digit", month: "short" }),
    year: "numeric",
    timeZone: "UTC",
  });
export const boundLabel = (r) => r.exact_bound || fraction(r.theta);
export const verifiedHere = (r) =>
  r.status === "framework-verified" || r.status === "verified";
export const statusLabel = (r) =>
  historicalBaseline(r)
    ? "Historical baseline"
    : r.status === "framework-verified"
      ? "Verified in our framework"
      : r.status === "verification-pending"
        ? "Verification pending"
        : "Comparator + NanoDa verified";
export function timelineRecords(records) {
  return records.map((r) => ({ ...r, first_verified_at: contributionDate(r) }));
}

export function validateCatalogue(data) {
  if (data.schema_version !== 1 || !Array.isArray(data.records))
    throw Error("Invalid catalogue");
  const ids = new Set();
  for (const r of data.records) {
    if (!/^[a-z0-9][a-z0-9-]+$/.test(r.id) || ids.has(r.id))
      throw Error("Invalid or duplicate catalogue ID");
    ids.add(r.id);
    rational(r.theta.numerator, r.theta.denominator);
    if (
      ![
        "framework-verified",
        "verification-pending",
        "historical-baseline",
      ].includes(r.status)
    )
      throw Error("Catalogue cannot mint signed verification status");
    if (
      !Number.isFinite(Date.parse(r.timeline_at)) ||
      !r.date_label ||
      !r.verification_note
    )
      throw Error("Missing date or verification context");
    if (r.status === "verification-pending" && r.first_verified_at)
      throw Error("Pending result cannot have a local verification date");
    if (
      historicalBaseline(r) &&
      (cmp(r.theta, { numerator: "1", denominator: "1" }) !== 0 ||
        r.first_verified_at ||
        r.receipt_url ||
        r.log_url)
    )
      throw Error(
        "Historical baseline must be theta = 1 without local or signed verification claims",
      );
    if (r.date_precision && !["day", "year"].includes(r.date_precision))
      throw Error("Unsupported catalogue date precision");
    if (
      r.date_precision === "year" &&
      !r.timeline_at.endsWith("-01-01T00:00:00Z")
    )
      throw Error("Year-only dates must use the start-of-year plotting anchor");
    if (
      r.status === "framework-verified" &&
      !Number.isFinite(Date.parse(r.first_verified_at))
    )
      throw Error("Missing framework check date");
    if (!r.authors?.length || !r.references?.length || !r.title || !r.method)
      throw Error("Missing attribution or evidence");
    for (const ref of r.references) {
      if (
        !/^https:\/\//.test(ref.url) &&
        !/^proofs\/[a-zA-Z0-9_./-]+$/.test(ref.url)
      )
        throw Error("Unsafe reference");
      if (ref.url.split("/").includes("..")) throw Error("Unsafe path");
    }
    if (r.exact_bound) {
      if (r.exact_bound !== "(1507 − 2√921) / 1653")
        throw Error(
          "Unsupported algebraic expression: provide exact interval validation",
        );
      const { lower, upper } = r.bound_interval || {};
      for (const q of [lower, upper]) rational(q.numerator, q.denominator);
      const delta = (q) => {
        const n = BigInt(q.numerator),
          d = BigInt(q.denominator),
          a = 1507n * d - 1653n * n;
        if (a <= 0n) throw Error("Algebraic interval outside positive branch");
        return a * a - 3684n * d * d;
      };
      if (
        delta(lower) < 0n ||
        delta(upper) > 0n ||
        cmp(lower, upper) >= 0 ||
        cmp(r.theta, upper) !== 0 ||
        cmp(sub(upper, lower), {
          numerator: "1",
          denominator: "1000000000000000000000000000000",
        }) > 0
      )
        throw Error("Invalid certified enclosure for Liu's bound");
    }
  }
  for (const r of data.records)
    for (const p of r.builds_on) {
      const parent = data.records.find((x) => x.id === p);
      if (!parent || parent.timeline_at >= r.timeline_at)
        throw Error("Unknown or later catalogue predecessor");
    }
  // Every displayed comparison must be decided exactly, even for algebraic entries.
  for (const a of data.records)
    for (const b of data.records) {
      if (a.id === b.id || (!a.bound_interval && !b.bound_interval)) continue;
      const alo = a.bound_interval?.lower || a.theta,
        ahi = a.bound_interval?.upper || a.theta;
      const blo = b.bound_interval?.lower || b.theta,
        bhi = b.bound_interval?.upper || b.theta;
      if (cmp(ahi, blo) >= 0 && cmp(bhi, alo) >= 0)
        throw Error("Overlapping bound intervals: refine before ranking");
    }
  return data;
}
