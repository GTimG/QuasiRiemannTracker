// Directory dates classify historical imports; proof requirements are unchanged.
export const isCalendarDate = (value) =>
  typeof value === "string" &&
  /^\d{4}-\d{2}-\d{2}$/.test(value) &&
  Number.isFinite(Date.parse(`${value}T00:00:00Z`)) &&
  new Date(`${value}T00:00:00Z`).toISOString().slice(0, 10) === value;

export function classifySubmissionDate(date, submittedAt) {
  if (!isCalendarDate(date)) throw Error("Invalid submission directory date");
  if (!Number.isFinite(Date.parse(submittedAt)))
    throw Error("Missing valid PR submission date");
  const prDate = new Date(submittedAt).toISOString().slice(0, 10);
  if (date > prDate)
    throw Error(
      `Submission directory date cannot be after the PR submission date ${prDate}`,
    );
  return { date, historical: date < prDate };
}
