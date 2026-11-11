// One pure record builder is shared by admission and catalogue generation, so
// successful proof admission cannot leave an entry that the website cannot use.
import {
  validateCatalogue,
  withSubmissionTimeline,
} from "../core/catalogue.mjs";
import {
  catalogueProofRecords,
  proofRevision,
} from "../core/catalogue-revisions.mjs";
import { fraction } from "../core/rational.mjs";
import { exactBound } from "../core/exact-bound.mjs";
import { certificate } from "./certificate.mjs";
import { validateSubmissionMetadata } from "./submission-metadata.mjs";
import {
  validSubmissionSourcePath,
  validateSubmissionDirectory,
} from "./submission-paths.mjs";

export function publicationRecord(admission, verification = admission) {
  const metadata = validateSubmissionMetadata(admission.metadata);
  const directory = /^submissions\/([^/]+)\/src$/.exec(
    admission.source_path ?? "",
  )?.[1];
  const directoryDate = /^(\d{4}-\d{2}-\d{2})-/.exec(directory ?? "")?.[1];
  if (directoryDate !== undefined)
    validateSubmissionDirectory(directory, {
      submittedAt: admission.pr.created_at,
    });
  // Metadata can be corrected in a later admitted rerun. Proof provenance is
  // taken from the earliest authenticated success for this identical revision.
  const evidence = certificate(verification.certificate);
  if (
    evidence.result_id !== admission.result_id ||
    evidence.theta_exact !== admission.theta_exact ||
    evidence.source_repository !== admission.repository ||
    evidence.source_commit !== admission.head_sha ||
    !validSubmissionSourcePath(admission.source_path, admission.result_id) ||
    verification.source_tree !== admission.source_tree
  )
    throw Error("Publication record differs from its verified source");
  const bound = exactBound(admission.theta_exact);
  const solution = `https://github.com/${admission.repository}/blob/${admission.head_sha}/${admission.source_path}/Candidate/Main.lean`;
  const certificateUrl = `certificates/${admission.result_id}.json`;
  return withSubmissionTimeline({
    id: admission.result_id,
    title: metadata.title,
    theta: bound.theta,
    ...(bound.exact_bound ? { exact_bound: bound.exact_bound } : {}),
    authors: metadata.authors,
    method: metadata.description,
    license: metadata.license || "See submitted source notices",
    builds_on: metadata.builds_on || [],
    status: "framework-verified",
    submitted_at: admission.pr.created_at,
    published_at: metadata.published_at || admission.pr.created_at,
    merged_at: admission.merged_at || "",
    pr: admission.number,
    repository: admission.repository,
    source_commit: admission.head_sha,
    first_verified_at: evidence.verified_at,
    timeline_at: metadata.published_at || admission.pr.created_at,
    date_label: "Public announcement",
    entrypoint: { module: "Candidate.Main", declaration: "Candidate.bound" },
    verification_note: `Comparator checked the canonical all-Dirichlet statement at ${bound.exact_bound ?? admission.theta_exact}${bound.exact_bound ? `, and that this bound is at most ${fraction(bound.theta)},` : ""} for the submitted commit. Lean, NanoDa and con-ron accepted the proof in the standard sandbox.`,
    certificate_url: certificateUrl,
    solution_url: solution,
    references: [
      ...new Map(
        [
          { label: "Verification record", url: certificateUrl },
          { label: "Checked Lean solution", url: solution },
          {
            label: "Reviewed submission",
            url: `https://github.com/${admission.repository}/pull/${admission.number}`,
          },
          ...(metadata.references || []),
        ].map((reference) => [reference.url, reference]),
      ).values(),
    ],
  });
}

// The protected prepare job's catalogue snapshot includes both displayed
// results and immutable historical revisions. A new declaration cannot reuse
// either namespace or reference a predecessor that is not already published.
export function validatePublication(catalogue, admission) {
  validateCatalogue(catalogue);
  const record = publicationRecord(admission);
  if (
    catalogueProofRecords(catalogue).some(
      (old) => old.id === record.id || proofRevision(old) === record.id,
    )
  )
    throw Error(`Result ID already published: ${record.id}`);
  for (const id of record.builds_on) {
    const predecessor = catalogue.records.find((old) => old.id === id);
    if (
      !predecessor ||
      Date.parse(predecessor.timeline_at) >= Date.parse(record.timeline_at)
    )
      throw Error(`Unknown or later catalogue predecessor: ${id}`);
  }
  validateCatalogue({ ...catalogue, records: [...catalogue.records, record] });
  return record;
}
