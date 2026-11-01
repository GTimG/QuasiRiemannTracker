import { decimal } from "../core/rational.mjs";
import {
  boundLabel,
  contributionDate,
  formatContributionDate,
  statusLabel,
  verifiedHere,
  historicalBaseline,
} from "../core/catalogue.mjs";
import CatalogueDetail from "./CatalogueDetail";
import type { Contribution } from "./types";

export type SortKey = "bound" | "author" | "date";
type Sort = { key: SortKey; direction: "ascending" | "descending" };
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
  const heading = (key: SortKey, label: string) => (
    <th scope="col" aria-sort={sort.key === key ? sort.direction : "none"}>
      <button
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
        {label}
        {sort.key === key ? (sort.direction === "ascending" ? " ↑" : " ↓") : ""}
      </button>
    </th>
  );
  return (
    <section className="panel contributor-board" aria-label="Submissions">
      <h2>Submissions</h2>
      <div className="contributor-scroll">
        <table>
          <thead>
            <tr>
              {heading("bound", "Bound θ")}
              {heading("author", "Author")}
              <th scope="col">Submission</th>
              {heading("date", "Date")}
            </tr>
          </thead>
          <tbody>
            {records.map((record) => (
              <Submission
                key={record.id}
                record={record}
                selected={selected}
                onSelect={onSelect}
                onNavigate={onNavigate}
              />
            ))}
          </tbody>
        </table>
      </div>
      {!records.length && <p>No submissions yet.</p>}
    </section>
  );
}
function Submission({
  record: r,
  selected,
  onSelect,
  onNavigate,
}: {
  record: Contribution;
  selected: string | null;
  onSelect: (id: string | null) => void;
  onNavigate: (id: string) => void;
}) {
  const expanded = selected === r.id;
  return (
    <>
      <tr id={`entry-${r.id}`}>
        <td title={boundLabel(r)}>
          {decimal(r.theta, 14)}
          <br />
          <small>{boundLabel(r)}</small>
        </td>
        <td>{r.authors.map((author) => author.name).join(", ")}</td>
        <td>
          <button
            id={`toggle-${r.id}`}
            className="contributor-bound"
            aria-expanded={expanded}
            aria-controls={expanded ? `details-${r.id}` : undefined}
            onClick={() => onSelect(expanded ? null : r.id)}
          >
            {r.title}
          </button>
          <br />
          {historicalBaseline(r) ? (
            <span className="tag historical">{statusLabel(r)}</span>
          ) : (
            <a
              className={`verification-badge ${verifiedHere(r) ? "teal" : "amber"}`}
              href={r.solution_url}
              target="_blank"
              rel="noreferrer"
            >
              <span>{statusLabel(r)}</span>
            </a>
          )}
        </td>
        <td>
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
        </td>
      </tr>
      {expanded && (
        <tr>
          <td colSpan={4} id={`details-${r.id}`}>
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
          </td>
        </tr>
      )}
    </>
  );
}
