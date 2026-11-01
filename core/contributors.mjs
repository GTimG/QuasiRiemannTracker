import { cmp, sub } from "./rational.mjs";
import { contributionDate } from "./catalogue.mjs";

// Credit each named coauthor with the submission's full chronological delta.
// The first entry has no predecessor and contributes zero.
export function contributorLeaderboard(records) {
  const people = new Map();
  const chronological = [...records].sort(
    (a, b) =>
      contributionDate(a).localeCompare(contributionDate(b)) ||
      a.id.localeCompare(b.id),
  );
  chronological.forEach((record, index) => {
    const delta = index
      ? sub(chronological[index - 1].theta, record.theta)
      : { numerator: "0", denominator: "1" };
    for (const author of new Map(
      record.authors.map((author) => [
        author.name.trim().toLocaleLowerCase(),
        author,
      ]),
    ).values()) {
      const key = author.name.trim().toLocaleLowerCase();
      let person = people.get(key);
      if (!person) {
        person = {
          name: author.name,
          improvement: { numerator: "0", denominator: "1" },
          best: record,
          count: 0,
          submissions: [],
          approximate: false,
        };
        people.set(key, person);
      }
      person.improvement = sub(
        person.improvement,
        sub({ numerator: "0", denominator: "1" }, delta),
      );
      person.count++;
      person.submissions.push({
        record,
        delta,
        approximate: Boolean(
          index && (record.exact_bound || chronological[index - 1].exact_bound),
        ),
      });
      person.approximate ||= Boolean(
        index && (record.exact_bound || chronological[index - 1].exact_bound),
      );
      if (cmp(record.theta, person.best.theta) < 0) person.best = record;
    }
  });
  return [...people.values()]
    .filter(
      (person) =>
        cmp(person.improvement, { numerator: "0", denominator: "1" }) > 0,
    )
    .sort(
      (a, b) =>
        cmp(b.improvement, a.improvement) ||
        cmp(a.best.theta, b.best.theta) ||
        a.name.localeCompare(b.name),
    );
}
