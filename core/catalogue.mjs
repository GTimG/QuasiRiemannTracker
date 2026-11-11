import { cmp, fraction, rational } from "./rational.mjs";
import { exactBound, witnessedBound } from "./exact-bound.mjs";
import {
  catalogueProofRecords,
  proofRevision,
} from "./catalogue-revisions.mjs";

export const contributionDate = (r) => r.timeline_at || r.first_verified_at;
// Normalize publication dates independently of submission and verification.
// A public PR is the default announcement when no earlier source is documented.
export function withSubmissionTimeline(record) {
  const hasPRDate =
    Number.isSafeInteger(record.pr) &&
    record.pr > 0 &&
    Number.isFinite(Date.parse(record.submitted_at));
  const publication =
    record.published_at ||
    (hasPRDate ? record.submitted_at : record.timeline_at);
  if (!Number.isFinite(Date.parse(publication)))
    throw Error("Missing valid public announcement date");
  const published_at = new Date(publication)
    .toISOString()
    .replace(/\.000Z$/, "Z");
  const { date_precision, ...rest } = record;
  return {
    ...rest,
    published_at,
    timeline_at: published_at,
    date_label: "Public announcement",
    ...((record.published_at || !hasPRDate) && date_precision
      ? { date_precision }
      : {}),
  };
}
export const historicalBaseline = (r) => r.status === "historical-baseline";
export const formatContributionDate = (r) =>
  new Date(contributionDate(r)).toLocaleDateString("en-GB", {
    ...(r.date_precision === "year" ? {} : { day: "2-digit", month: "short" }),
    year: "numeric",
    timeZone: "UTC",
  });
// Calendar anchors are plotting coordinates, not observed midnight timestamps.
export const contributionDateValue = (r) =>
  r.date_precision === "year"
    ? contributionDate(r).slice(0, 4)
    : r.date_precision === "day"
      ? contributionDate(r).slice(0, 10)
      : contributionDate(r);
export const contributionDateTitle = (r) =>
  `${r.date_label || "Public announcement"}: ${contributionDateValue(r)}${r.date_precision ? ` (${r.date_precision} only)` : ""}`;
// Display label: the exact expression when there is one.
export const boundLabel = (r) => r.exact_bound || fraction(r.theta);
// Verification identity (theta_exact): an exact expression is keyed together
// with the proved rational upper bound that is ranked.
export const boundKey = (r) =>
  r.exact_bound ? witnessedBound(r.exact_bound, r.theta) : fraction(r.theta);
export const verifiedHere = (r) =>
  r.status === "accepted" ||
  r.status === "framework-verified" ||
  r.status === "verified";
export const statusLabel = (r) =>
  historicalBaseline(r)
    ? "Historical baseline"
    : r.status === "accepted" || r.status === "framework-verified"
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
  const proofRecords = catalogueProofRecords(data);
  if (
    new Set(data.records.map((record) => record.id)).size !==
    data.records.length
  )
    throw Error("Invalid or duplicate catalogue ID");
  for (const r of proofRecords) {
    if (r.published_at && !Number.isFinite(Date.parse(r.published_at)))
      throw Error("Invalid public announcement date");
    if (!/^[a-z0-9][a-z0-9-]+$/.test(r.id) || ids.has(proofRevision(r)))
      throw Error("Invalid or duplicate catalogue ID");
    ids.add(proofRevision(r));
    rational(r.theta.numerator, r.theta.denominator);
    if (
      ![
        "accepted",
        "framework-verified",
        "verification-pending",
        "historical-baseline",
      ].includes(r.status)
    )
      throw Error("Unsupported catalogue verification status");
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
        !/^certificates\/[a-z0-9-]+\.json$/.test(ref.url)
      )
        throw Error("Unsafe reference");
      if (ref.url.split("/").includes("..")) throw Error("Unsafe path");
    }
    // An exact expression must be canonical; theta is its proved upper bound.
    if (r.exact_bound) exactBound(boundKey(r));
  }
  const currentById = new Map(
    data.records.map((record) => [record.id, record]),
  );
  const utcDay = (at) => new Date(at).toISOString().slice(0, 10);
  for (const r of proofRecords)
    for (const p of r.builds_on) {
      const parent = currentById.get(p);
      if (!parent) throw Error("Unknown or later catalogue predecessor");
      // Accepted imports can record only a calendar day. Do not invent an
      // order within that day when crediting a predecessor.
      const dayPrecision =
        r.status === "accepted" || parent.status === "accepted";
      if (
        dayPrecision
          ? utcDay(parent.timeline_at) > utcDay(r.timeline_at)
          : Date.parse(parent.timeline_at) >= Date.parse(r.timeline_at)
      )
        throw Error("Unknown or later catalogue predecessor");
    }
  const visiting = new Set(),
    checked = new Set();
  const checkCycles = (record) => {
    if (visiting.has(record)) throw Error("Cyclic catalogue predecessors");
    if (checked.has(record)) return;
    visiting.add(record);
    for (const id of record.builds_on) checkCycles(currentById.get(id));
    visiting.delete(record);
    checked.add(record);
  };
  for (const record of proofRecords) checkCycles(record);
  return data;
}
