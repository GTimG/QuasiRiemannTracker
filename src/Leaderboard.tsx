import {
  BadgeCheck,
  ChevronDown,
  Clock,
  ExternalLink,
  FileCheck2,
} from "lucide-react";
import { decimal } from "../core/rational.mjs";
import {
  boundLabel,
  contributionDate,
  formatContributionDate,
  historicalBaseline,
  statusLabel,
  verifiedHere,
} from "../core/catalogue.mjs";
import CatalogueDetail from "./CatalogueDetail";
import type { Contribution } from "./types";
import { publicUrl } from "./urls";

export type SortKey = "bound" | "author" | "date";
type Sort = { key: SortKey; direction: "ascending" | "descending" };
const columns: { key: SortKey; label: string }[] = [
  { key: "bound", label: "Exact bound θ" },
  { key: "author", label: "Author" },
  { key: "date", label: "Date" },
];
const projectUrl = (r: Contribution) => {
  if (r.repository) return `https://github.com/${r.repository}`;
  const publication = r.references.find((ref) =>
    /publication|paper|manuscript|writeup|homepage/i.test(ref.label),
  );
  if (publication) return publicUrl(publication.url);
};

export default function Leaderboard({
  records,
  selected,
  onSelect,
  onNavigate,
  sort,
  onSort,
}: {
  records: Contribution[];
  selected: string | null;
  onSelect: (id: string | null) => void;
  onNavigate: (id: string) => void;
  sort: Sort;
  onSort: (sort: Sort) => void;
}) {
  return (
    <section className="panel contribution-list" aria-label="Leaderboard">
      <div
        className="leaderboard-sort"
        role="group"
        aria-label="Sort contributions"
      >
        <span>Sort by</span>
        {columns.map(({ key, label }) => (
          <button
            key={key}
            aria-label={label}
            aria-pressed={sort.key === key}
            onClick={() =>
              onSort({
                key,
                direction:
                  sort.key === key && sort.direction === "ascending"
                    ? "descending"
                    : "ascending",
              })
            }
          >
            {key === "bound" ? "Bound" : label}
            {sort.key === key && (
              <>
                <span aria-hidden="true">
                  {sort.direction === "ascending" ? "↑" : "↓"}
                </span>
                <span className="sr-only">{sort.direction}</span>
              </>
            )}
          </button>
        ))}
      </div>
      <ol className="leaderboard" aria-label="Contributions">
        {records.map((r) => {
          const expanded = selected === r.id;
          const authors = r.authors.map((a) => a.name).join(", ");
          const homepage = projectUrl(r);
          return (
            <li
              key={r.id}
              id={`entry-${r.id}`}
              className={`leaderboard-entry${r.is_record ? "" : " off-frontier"}`}
            >
              <div className="entry-summary">
                <button
                  id={`toggle-${r.id}`}
                  className="entry-toggle"
                  aria-label={r.title}
                  aria-describedby={`meta-${r.id} frontier-${r.id}`}
                  aria-expanded={expanded}
                  aria-controls={expanded ? `details-${r.id}` : undefined}
                  onClick={() => onSelect(expanded ? null : r.id)}
                >
                  <span className="entry-heading">
                    <span className="entry-decimal">
                      {decimal(r.theta, 14)}
                    </span>
                    <ChevronDown
                      size={16}
                      className="entry-chevron"
                      aria-hidden="true"
                    />
                  </span>
                  <span id={`meta-${r.id}`} className="entry-meta">
                    <span className="entry-author" title={authors}>
                      {authors}
                    </span>
                    <span className="entry-exact" title={boundLabel(r)}>
                      {boundLabel(r)}
                    </span>
                    <time
                      dateTime={
                        r.date_precision === "year"
                          ? contributionDate(r).slice(0, 4)
                          : contributionDate(r)
                      }
                      title={`${r.date_label || "First verified"}: ${contributionDate(r)}`}
                    >
                      {formatContributionDate(r)}
                    </time>
                  </span>
                  <span className="entry-method">{r.method}</span>
                  <span id={`frontier-${r.id}`} className="sr-only">
                    {r.is_record
                      ? "On the verified frontier"
                      : "Outside the verified frontier"}
                  </span>
                </button>
                <div className="entry-actions">
                  {historicalBaseline(r) ? (
                    <span className="tag historical" title={statusLabel(r)}>
                      <Clock size={18} aria-hidden="true" />
                      <span className="sr-only">{statusLabel(r)}</span>
                    </span>
                  ) : (
                    <a
                      className={`tag verification-badge ${verifiedHere(r) ? "teal" : "amber"}`}
                      title={statusLabel(r)}
                      aria-label={`Checked solution for ${r.title}`}
                      href={r.solution_url}
                      target="_blank"
                      rel="noreferrer"
                    >
                      {verifiedHere(r) ? (
                        <BadgeCheck size={18} aria-hidden="true" />
                      ) : (
                        <Clock size={18} aria-hidden="true" />
                      )}
                      <span className="sr-only">{statusLabel(r)}</span>
                    </a>
                  )}
                  {homepage && (
                    <a
                      className="source-link"
                      href={homepage}
                      aria-label={`Project homepage for ${r.title}`}
                      title="Project homepage"
                      target="_blank"
                      rel="noreferrer"
                    >
                      <ExternalLink size={16} aria-hidden="true" />
                    </a>
                  )}
                </div>
              </div>
              {expanded && (
                <div id={`details-${r.id}`} className="entry-details">
                  <CatalogueDetail
                    record={r}
                    onClose={() => {
                      onSelect(null);
                      document
                        .getElementById(`toggle-${r.id}`)
                        ?.focus({ preventScroll: true });
                    }}
                    onSelect={onNavigate}
                  />
                </div>
              )}
            </li>
          );
        })}
      </ol>
      {!records.length && (
        <div className="empty-table">
          <FileCheck2 size={24} />
          <h3>No active contributions yet</h3>
        </div>
      )}
    </section>
  );
}
