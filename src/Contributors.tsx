import { Fragment, useState } from "react";
import { contributorLeaderboard } from "../core/contributors.mjs";
import { decimal, fraction, scientific } from "../core/rational.mjs";
import { boundLabel, formatContributionDate } from "../core/catalogue.mjs";
import type { Contribution, Rational } from "./types";

export default function Contributors({
  records,
  onSelect,
  submissionsHref,
}: {
  records: Contribution[];
  onSelect: (id: string) => void;
  submissionsHref: string;
}) {
  const [expanded, setExpanded] = useState<string | null>(null);
  const people = contributorLeaderboard(records);
  const submissionLink = (record: Contribution, label: string) => (
    <a
      href={`${submissionsHref}#entry-${record.id}`}
      onClick={(event) => {
        if (
          event.button ||
          event.metaKey ||
          event.ctrlKey ||
          event.shiftKey ||
          event.altKey
        )
          return;
        event.preventDefault();
        onSelect(record.id);
      }}
    >
      {label}
    </a>
  );
  return (
    <section
      className="panel contributor-board"
      aria-label="Contributor leaderboard"
    >
      <h2>Contributor leaderboard</h2>
      <p className="muted">
        Ranked by the sum of submission improvements. Each coauthor receives the
        full delta; the first submission contributes zero.
      </p>
      <div className="contributor-scroll">
        <table>
          <thead>
            <tr>
              <th scope="col">Rank</th>
              <th scope="col">Contributor</th>
              <th scope="col">Total improvement</th>
              <th scope="col">Submissions</th>
              <th scope="col">Best bound θ</th>
            </tr>
          </thead>
          <tbody>
            {people.map((person, index) => (
              <Fragment key={person.name}>
                <tr className="contributor-summary">
                  <td>{index + 1}</td>
                  <th scope="row">
                    <button
                      className="contributor-bound"
                      aria-expanded={expanded === person.name}
                      onClick={() =>
                        setExpanded(
                          expanded === person.name ? null : person.name,
                        )
                      }
                    >
                      {person.name} {expanded === person.name ? "▴" : "▾"}
                    </button>
                  </th>
                  <td title={fraction(person.improvement)}>
                    Δ {person.approximate ? "≈ " : ""}
                    {scientific(person.improvement)}
                  </td>
                  <td>{person.count}</td>
                  <td title={boundLabel(person.best)}>
                    {submissionLink(
                      person.best,
                      decimal(person.best.theta, 14),
                    )}
                  </td>
                </tr>
                {expanded === person.name &&
                  person.submissions.map(
                    ({
                      record,
                      delta,
                      approximate,
                    }: {
                      record: Contribution;
                      delta: Rational;
                      approximate: boolean;
                    }) => (
                      <tr className="contributor-submission" key={record.id}>
                        <td aria-hidden="true">↳</td>
                        <th scope="row">
                          {submissionLink(record, record.title)}
                        </th>
                        <td title={fraction(delta)}>
                          Δ {approximate ? "≈ " : ""}
                          {scientific(delta)}
                        </td>
                        <td>{formatContributionDate(record)}</td>
                        <td title={boundLabel(record)}>
                          {submissionLink(record, decimal(record.theta, 14))}
                        </td>
                      </tr>
                    ),
                  )}
              </Fragment>
            ))}
          </tbody>
        </table>
      </div>
    </section>
  );
}
