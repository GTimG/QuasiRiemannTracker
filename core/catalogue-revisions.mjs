// A displayed catalogue entry may point to a newer immutable proof revision.
// Historical metadata continues to be checked, but is not plotted as a new result.
const REVISIONS = new Map([
  ["nielstron-20261009-tightening", "nielstron-algebraic-20261009"],
]);

export const proofRevision = (record) => record.proof_revision || record.id;

export function catalogueProofRecords(catalogue) {
  const live = catalogue.records;
  const history = catalogue.historical_records || [];
  if (!Array.isArray(live) || !Array.isArray(history))
    throw Error("Invalid catalogue revision lists");
  for (const record of [...live, ...history]) {
    if (!Number.isFinite(Date.parse(record.timeline_at)))
      throw Error("Invalid catalogue revision timestamp");
    if (Object.hasOwn(record, "proof_revision") &&
        REVISIONS.get(record.id) !== record.proof_revision)
      throw Error("Unreviewed catalogue proof revision");
  }
  for (const old of history) {
    const current = live.find((record) => record.id === old.id);
    if (!current || !current.proof_revision ||
        Date.parse(old.timeline_at) >= Date.parse(current.timeline_at))
      throw Error("Historical revision must precede its current catalogue entry");
  }
  for (const current of live) {
    if (current.proof_revision &&
        !history.some((old) => old.id === current.id && proofRevision(old) === current.id))
      throw Error("Revised catalogue entry is missing its original metadata");
  }
  const records = [...live, ...history];
  const ids = records.map(proofRevision);
  if (new Set(ids).size !== ids.length)
    throw Error("Duplicate catalogue proof revision");
  return records;
}

export function findProofRevision(catalogue, id) {
  return catalogueProofRecords(catalogue).find((record) => proofRevision(record) === id);
}
