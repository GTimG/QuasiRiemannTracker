import { useState } from "react";
import { ChevronDown } from "lucide-react";
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
      className="panel contribution-list contributor-board"
      aria-label="Contributor leaderboard"
    >
      <h2>Contributor leaderboard</h2>
      <div className="contributor-scores contributor-columns">
        <span>Total Δ</span>
        <span>Best θ</span>
      </div>
      <ol className="leaderboard" aria-label="Contributors">
        {people.map((person, index) => (
          <li className="leaderboard-entry" key={person.name}>
            <button
              className="entry-toggle contributor-summary"
              aria-expanded={expanded === person.name}
              onClick={() =>
                setExpanded(expanded === person.name ? null : person.name)
              }
            >
              <span className="contributor-name">
                <span className="muted">{index + 1}.</span> {person.name}
                <ChevronDown
                  size={16}
                  className="entry-chevron"
                  aria-hidden="true"
                />
              </span>
              <span className="contributor-scores">
                <span
                  className="contributor-improvement"
                  title={fraction(person.improvement)}
                >
                  <span className="entry-decimal">
                    Δ {person.approximate ? "≈ " : ""}
                    {scientific(person.improvement)}
                  </span>
                </span>
                <span
                  className="contributor-best"
                  title={boundLabel(person.best)}
                >
                  <span>{decimal(person.best.theta, 14)}</span>
                </span>
              </span>
              <span className="entry-meta">
                {person.count}{" "}
                {person.count === 1 ? "submission" : "submissions"}
              </span>
            </button>
            {expanded === person.name && (
              <ol className="contributor-submissions">
                {person.submissions.map(
                  ({
                    record,
                    delta,
                    approximate,
                  }: {
                    record: Contribution;
                    delta: Rational;
                    approximate: boolean;
                  }) => (
                    <li className="contributor-submission" key={record.id}>
                      <span className="contributor-submission-title">
                        {submissionLink(record, record.title)}
                      </span>
                      <span className="contributor-scores">
                        <span title={fraction(delta)}>
                          Δ {approximate ? "≈ " : ""}
                          {scientific(delta)}
                        </span>
                        <span title={boundLabel(record)}>
                          {submissionLink(record, decimal(record.theta, 14))}
                        </span>
                      </span>
                      <time className="contributor-caption">
                        {formatContributionDate(record)}
                      </time>
                    </li>
                  ),
                )}
              </ol>
            )}
          </li>
        ))}
      </ol>
    </section>
  );
}
