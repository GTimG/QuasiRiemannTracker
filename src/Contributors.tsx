import { useState } from "react";
import { MathJax } from "better-react-mathjax";
import { ChevronDown } from "lucide-react";
import { contributorLeaderboard } from "../core/contributors.mjs";
import { decimal, fraction, scientific } from "../core/rational.mjs";
import { boundLabel, formatContributionDate } from "../core/catalogue.mjs";
import type { Contribution, Rational } from "./types";

function DeltaMath({
  value,
  prefix = false,
}: {
  value: Rational;
  prefix?: boolean;
}) {
  const formatted = scientific(value).replace(
    /e([+-]?\d+)$/,
    String.raw`\times 10^{$1}`,
  );
  return (
    <MathJax
      inline
      dynamic
    >{`\\(${prefix ? "\\Delta " : ""}${formatted}\\)`}</MathJax>
  );
}

export default function Contributors({
  records,
  onSelect,
  submissionsHref,
  seeAll,
  height,
  limit,
}: {
  records: Contribution[];
  onSelect: (id: string) => void;
  submissionsHref: string;
  /** Boxed front-page variant: fixed height, the list scrolls inside. */
  height?: number;
  /** Show only the top contributors (used where scrolling would get in the way). */
  limit?: number;
  seeAll?: {
    href: string;
    onClick: (event: React.MouseEvent<HTMLAnchorElement>) => void;
  };
}) {
  const [expanded, setExpanded] = useState<string | null>(null);
  const people = contributorLeaderboard(records).slice(0, limit);
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
      style={height ? { height } : undefined}
      className={`panel contribution-list contributor-board${seeAll ? " boxed" : ""}`}
      aria-label="Contributor leaderboard"
    >
      <div className="contributor-header">
        <span className="section-title">
          <strong>Contributors</strong>
          {seeAll && (
            <a className="see-all" href={seeAll.href} onClick={seeAll.onClick}>
              See all
            </a>
          )}
        </span>
        <span>
          Total <MathJax inline>{String.raw`\(\Delta\)`}</MathJax>
        </span>
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
                <span className="muted">{index + 1}.</span>
                <span className="contributor-label" title={person.name}>
                  {person.name}
                </span>
                <span className="contributor-count">{person.count}</span>
              </span>
              <span className="contributor-total">
                <span
                  className="contributor-improvement"
                  title={fraction(person.improvement)}
                >
                  <span className="entry-decimal">
                    <DeltaMath value={person.improvement} />
                  </span>
                </span>
                <ChevronDown
                  size={16}
                  className="entry-chevron"
                  aria-hidden="true"
                />
              </span>
            </button>
            {expanded === person.name && (
              <ol className="contributor-submissions">
                {person.submissions.map(
                  ({
                    record,
                    delta,
                  }: {
                    record: Contribution;
                    delta: Rational;
                  }) => (
                    <li className="contributor-submission" key={record.id}>
                      <span className="contributor-submission-title">
                        {submissionLink(record, record.title)}
                      </span>
                      <span className="contributor-scores">
                        <span title={fraction(delta)}>
                          <DeltaMath value={delta} prefix />
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
