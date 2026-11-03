import legacyDirectories from "./submission-directories.json" with { type: "json" };
import {
  classifySubmissionDate,
  isCalendarDate,
} from "../core/historical-submission.mjs";

// Preserve IDs, Lean namespaces and immutable receipts from before the folder
// migration. Four original imports without a PR use their recorded release date.
// The table also retains IDs for submissions already open during the migration.
const legacyIds = new Map(
  Object.entries(legacyDirectories).map(([id, directory]) => [directory, id]),
);
const idPattern = /^[a-z][a-z0-9-]{2,63}$/;
const datedPattern = /^(\d{4}-\d{2}-\d{2})-([a-z][a-z0-9-]{2,63})$/;
const dateToken = /(?:^|-)(\d{4})-?(\d{2})-?(\d{2})(?=-|$)/g;
const validDate = isCalendarDate;

export function validateSubmissionDirectory(directory, { submittedAt } = {}) {
  const match = typeof directory === "string" && datedPattern.exec(directory);
  if (
    !match ||
    !validDate(match[1]) ||
    [...match[2].matchAll(dateToken)].some(([, year, month, day]) =>
      validDate(`${year}-${month}-${day}`),
    )
  )
    throw Error(
      `Invalid submission directory: ${directory}; use YYYY-MM-DD-<result-id> with the date only once`,
    );
  if (submittedAt !== undefined) classifySubmissionDate(match[1], submittedAt);
  const id = legacyIds.get(directory) ?? match[2];
  if (
    Object.hasOwn(legacyDirectories, id) &&
    legacyDirectories[id] !== directory
  )
    throw Error(
      `Use the original submission directory ${legacyDirectories[id]} for ${id}`,
    );
  return directory;
}

export function submissionId(directory) {
  // Old Git commits and their archived source paths remain valid evidence.
  if (typeof directory === "string" && idPattern.test(directory))
    return directory;
  validateSubmissionDirectory(directory);
  return legacyIds.get(directory) ?? datedPattern.exec(directory)[2];
}

export function submissionDirectories(names) {
  const directories = new Map();
  for (const directory of names) {
    const id = submissionId(directory);
    if (directories.has(id))
      throw Error(`Duplicate submission directories for ${id}`);
    directories.set(id, directory);
  }
  return directories;
}

export function submissionDirectory(id, names) {
  const directory = submissionDirectories(names).get(id);
  if (!directory) throw Error(`Missing submission directory for ${id}`);
  return directory;
}

export function validSubmissionSourcePath(path, id) {
  const match = /^submissions\/([^/]+)\/src$/.exec(path ?? "");
  try {
    return !!match && submissionId(match[1]) === id;
  } catch {
    return false;
  }
}
