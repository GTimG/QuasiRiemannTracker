import { useEffect, useMemo, useRef, useState } from "react";
import { MathJax } from "better-react-mathjax";
import {
  ExternalLink,
  GitBranch,
  Github,
  GitPullRequest,
  BadgeCheck,
  Clock,
  X,
  FileCheck2,
} from "lucide-react";
import Chart from "./Chart";
import { cmp, decimal, fraction, recordHistory } from "../core/rational.mjs";
import type { Contribution, Registry } from "./types";
import {
  contributionDate,
  boundLabel,
  verifiedHere,
  statusLabel,
  timelineRecords,
} from "../core/catalogue.mjs";
import { publicUrl } from "./urls";
import CatalogueDetail from "./CatalogueDetail";
import LeanCode from "./LeanCode";
const upstream =
  "https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/";
const initial: Registry = {
  records: [],
  events: [],
  active_ids: [],
  baseline_status: "infrastructure-blocked",
};
const date = (s: string) =>
  new Date(s).toLocaleDateString("en-GB", {
    day: "2-digit",
    month: "short",
    year: "numeric",
    timeZone: "UTC",
  });
const timestamp = (s: string) =>
  new Date(s)
    .toISOString()
    .replace("T", " ")
    .replace(".000Z", "Z")
    .replace("Z", " UTC");
type SortKey = "title" | "author" | "bound" | "date";
const contributionTitle = (r: Contribution) =>
  r.title.includes(" · ") ? r.title.split(" · ").slice(1).join(" · ") : r.title;
const columns: { key: SortKey; label: string }[] = [
  { key: "title", label: "Contribution" },
  { key: "author", label: "Author" },
  { key: "bound", label: "Exact bound θ" },
  { key: "date", label: "Publication" },
];
const theorem = `∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},\n  (θ < s.re) → ¬ (χ = 1 ∧ s = 1) →\n  DirichletCharacter.LFunction χ s ≠ 0`;
const leanTheorem = `theorem quasi_riemann_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (θ : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    LFunction χ s ≠ 0 := by
  sorry`;
export default function App() {
  const [registry, setRegistry] = useState<Registry>(initial),
    [catalogue, setCatalogue] = useState<Contribution[]>([]),
    [repository, setRepository] = useState<string | null>(null),
    [tab, setTab] = useState("Timeline"),
    [sort, setSort] = useState<{
      key: SortKey;
      direction: "ascending" | "descending";
    }>({ key: "bound", direction: "ascending" }),
    [selected, setSelected] = useState<string | null>(null),
    [error, setError] = useState(""),
    [modal, setModal] = useState<"submit" | "policy" | null>(null);
  const dialog = useRef<HTMLDialogElement>(null);
  useEffect(() => {
    const read = (name: string) =>
      fetch(publicUrl(name)).then((r) => {
        if (!r.ok) throw Error(`Could not load ${name}`);
        return r.json();
      });
    Promise.all([
      read("registry.json"),
      read("catalogue.json"),
      read("site.json"),
    ])
      .then(([r, c, config]) => {
        if (
          r.schema_version !== 1 ||
          !Array.isArray(r.records) ||
          c.schema_version !== 1 ||
          !Array.isArray(c.records)
        )
          throw Error("Unsupported research data.");
        setRegistry(r);
        setCatalogue(c.records);
        setRepository(config.repository);
      })
      .catch((e) => setError(e.message));
  }, []);
  useEffect(() => {
    if (modal && !dialog.current?.open) dialog.current?.showModal();
    if (!modal && dialog.current?.open) dialog.current?.close();
  }, [modal]);
  const combined = [
    ...new Map(
      [...catalogue, ...registry.records].map((r) => [r.id, r]),
    ).values(),
  ];
  const ranked = new Map(
    recordHistory(timelineRecords(combined.filter(verifiedHere))).map((r) => [
      r.id,
      r.is_record,
    ]),
  );
  const all = combined.map((r) => ({
      ...r,
      is_record: ranked.get(r.id) === true,
    })),
    events = registry.events,
    withdrawn = new Set(events.map((e) => e.id));
  const commissioned = registry.records.length > 0;
  const records = useMemo(
    () =>
      all
        .filter((r) => !withdrawn.has(r.id))
        .sort((a, b) => {
          const comparison =
            sort.key === "bound"
              ? cmp(a.theta, b.theta)
              : sort.key === "title"
                ? contributionTitle(a).localeCompare(contributionTitle(b))
                : sort.key === "author"
                  ? a.authors
                      .map((author) => author.name)
                      .join(", ")
                      .localeCompare(
                        b.authors.map((author) => author.name).join(", "),
                      )
                  : contributionDate(a).localeCompare(contributionDate(b));
          return comparison * (sort.direction === "ascending" ? 1 : -1);
        }),
    [all, sort, events],
  );
  const active = all.filter((r) => !withdrawn.has(r.id)),
    best = [...active]
      .filter(verifiedHere)
      .sort((a, b) => cmp(a.theta, b.theta))[0],
    detail = all.find((r) => r.id === selected);
  useEffect(() => {
    const context = (
      document as Document & {
        modelContext?: {
          registerTool: (tool: unknown, options: unknown) => Promise<void>;
        };
      }
    ).modelContext;
    if (!context) return;
    const controller = new AbortController();
    void Promise.resolve(
      context.registerTool(
        {
          name: "inspect_qrh_contribution",
          description:
            "Select an existing contribution in the catalogue. Does not publish or verify proofs.",
          inputSchema: {
            type: "object",
            properties: { id: { type: "string" } },
            required: ["id"],
            additionalProperties: false,
          },
          annotations: { readOnlyHint: false, untrustedContentHint: true },
          execute: async (input: unknown) => {
            if (
              !input ||
              typeof input !== "object" ||
              Object.keys(input).join() !== "id" ||
              !("id" in input) ||
              typeof input.id !== "string"
            )
              throw Error("Expected a contribution ID");
            const r = all.find((r) => r.id === input.id);
            if (!r) throw Error("Unknown contribution");
            setSelected(r.id);
            await new Promise(requestAnimationFrame);
            return { id: r.id, theta: r.theta };
          },
        },
        { signal: controller.signal },
      ),
    ).catch(() => {});
    return () => controller.abort();
  }, [all]);
  return (
    <div className="shell">
      <main id="main">
        <header className="topbar">
          <a className="brand" href="#main" onClick={() => setTab("Timeline")}>
            <img src={publicUrl("favicon.svg")} alt="" width="36" height="36" />
            QRH Leaderboard
          </a>
          <div className="header-links">
            {repository && (
              <a
                className="github-badge"
                href={`https://github.com/${repository}`}
                target="_blank"
                rel="noreferrer"
              >
                <Github size={16} aria-hidden="true" />
                GitHub
              </a>
            )}
            <button
              className="pr-button"
              aria-label="Submit a proof"
              title="Submit a proof"
              onClick={() => setModal("submit")}
            >
              <GitPullRequest size={19} aria-hidden="true" />
              <span>Submit</span>
            </button>
          </div>
        </header>
        <div className="content">
          <section
            className="bound-summary"
            aria-label="Quasi-Riemann hypothesis and current bound"
          >
            <div className="qrh-statement">
              <h1 className="statement-description">
                All nontrivial zeros of Dirichlet L-functions lie in the strip{" "}
                <MathJax
                  inline
                >{String.raw`\(\operatorname{Re}(s)\in[1-\theta,\theta]\)`}</MathJax>
                .
              </h1>
            </div>
            <div className="current-bound">
              {best ? (
                <button
                  className="best-bound"
                  aria-label="View best verified proof"
                  onClick={() => setSelected(best.id)}
                >
                  <MathJax dynamic>
                    {`\\(\\theta \\le ${decimal(best.theta, 16).replace("…", "\\ldots")}\\)`}
                  </MathJax>
                </button>
              ) : (
                <p className="muted">No verified bound yet.</p>
              )}
            </div>
          </section>
          <nav className="view-nav" aria-label="Research views">
            {["Timeline", "Contributions", "Protocol"].map((name) => (
              <button
                key={name}
                aria-current={tab === name ? "page" : undefined}
                onClick={() => setTab(name)}
              >
                {name}
                {name === "Contributions" && <small>{all.length}</small>}
              </button>
            ))}
          </nav>
          {error && (
            <div className="notice error" role="alert">
              {error}
            </div>
          )}
          {tab === "Protocol" ? (
            <Protocol commissioned={commissioned} />
          ) : (
            <>
              <div
                className={"research-layout" + (detail ? " has-detail" : "")}
              >
                <div className="research-main">
                  {tab === "Timeline" && (
                    <Chart
                      records={records}
                      allRecords={all}
                      events={events}
                      selected={selected}
                      onSelect={(r) => setSelected(r.id)}
                    />
                  )}{" "}
                  <section className="panel contribution-table">
                    <div className="panel-heading">
                      <div>
                        <h2>
                          Contributions{" "}
                          <span className="count">{records.length}</span>
                        </h2>
                      </div>
                    </div>
                    <div className="table-scroll">
                      <table role="table">
                        <caption className="sr-only">
                          Equivalent keyboard-accessible table of every plotted
                          contribution
                        </caption>
                        <thead>
                          <tr>
                            {columns.map(({ key, label }) => (
                              <th
                                key={key}
                                scope="col"
                                aria-sort={
                                  sort.key === key ? sort.direction : "none"
                                }
                              >
                                <button
                                  onClick={() =>
                                    setSort({
                                      key,
                                      direction:
                                        sort.key === key &&
                                        sort.direction === "ascending"
                                          ? "descending"
                                          : "ascending",
                                    })
                                  }
                                >
                                  {label}
                                  {sort.key === key && (
                                    <span aria-hidden="true">
                                      {sort.direction === "ascending"
                                        ? "↑"
                                        : "↓"}
                                    </span>
                                  )}
                                </button>
                              </th>
                            ))}
                          </tr>
                        </thead>
                        <tbody>
                          {records.map((r) => (
                            <tr
                              key={r.id}
                              className={
                                selected === r.id ? "selected-row" : ""
                              }
                            >
                              <td data-label="Contribution">
                                <div className="contribution-name">
                                  <button
                                    className="row-title"
                                    aria-label={r.title}
                                    onClick={() => setSelected(r.id)}
                                  >
                                    {contributionTitle(r)}
                                  </button>
                                  <button
                                    className={
                                      "tag verification-badge " +
                                      (verifiedHere(r) ? "teal" : "amber")
                                    }
                                    title={statusLabel(r)}
                                    aria-label={`Read verification protocol for ${contributionTitle(r)}`}
                                    onClick={() => setTab("Protocol")}
                                  >
                                    {verifiedHere(r) ? (
                                      <BadgeCheck
                                        size={18}
                                        aria-hidden="true"
                                      />
                                    ) : (
                                      <Clock size={18} aria-hidden="true" />
                                    )}
                                    <span className="sr-only">
                                      {statusLabel(r)}
                                    </span>
                                  </button>
                                </div>
                              </td>
                              <td data-label="Author" className="author-cell">
                                {r.authors.map((a) => a.name).join(", ")}
                              </td>
                              <td
                                data-label="Exact bound θ"
                                className="fraction-cell"
                              >
                                {boundLabel(r)}
                                <small>{decimal(r.theta, 14)}</small>
                              </td>
                              <td data-label="Publication">
                                <time
                                  dateTime={contributionDate(r)}
                                  title={timestamp(contributionDate(r))}
                                >
                                  {date(contributionDate(r))}
                                </time>
                              </td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                    {!records.length && (
                      <div className="empty-table">
                        <FileCheck2 size={24} />
                        <h3>No active contributions yet</h3>
                        <p>
                          Successful Lean and NanoDa checks, followed by
                          attribution review, unlock publication.
                        </p>
                      </div>
                    )}
                  </section>
                </div>
                {detail && (
                  <aside className="details" aria-live="polite">
                    <ProofDetail
                      record={detail}
                      onClose={() => setSelected(null)}
                      onSelect={(id) => setSelected(id)}
                      events={events}
                    />
                  </aside>
                )}
              </div>
              {events.length > 0 && (
                <section className="panel event-list">
                  <h2>Registry events</h2>
                  {events.map((e, i) => (
                    <p key={i}>
                      {date(e.at)} · {e.type} · {e.id}: {e.reason}
                    </p>
                  ))}
                </section>
              )}
            </>
          )}
        </div>
      </main>
      <dialog
        ref={dialog}
        onCancel={() => setModal(null)}
        onClick={(e) => {
          if (e.target === e.currentTarget) setModal(null);
        }}
      >
        <button
          className="dialog-close icon"
          aria-label="Close dialog"
          onClick={() => setModal(null)}
        >
          <X size={20} />
        </button>
        {modal === "submit" ? (
          <>
            <h2>Contribute a result</h2>
            <p>
              Open a GitHub pull request with the exact bound, author names,
              source links and verification evidence. Include Lean source for a
              new proof.
            </p>
            <ol className="guide-list">
              <li>
                Add the result to <code>catalogue/results.json</code>.
              </li>
              <li>Open a pull request. Website checks run automatically.</li>
              <li>
                After review and merge, the website updates automatically.
              </li>
            </ol>
            <p className="notice-text">
              {repository ? (
                <a
                  href={`https://github.com/${repository}/compare`}
                  target="_blank"
                  rel="noreferrer"
                >
                  Open a pull request on GitHub
                </a>
              ) : (
                "The repository link will appear here once it is connected."
              )}{" "}
              Results awaiting independent checks are marked “Verification
              pending”.
            </p>
          </>
        ) : modal === "policy" ? (
          <>
            <h2>Verification details</h2>
            <Protocol commissioned={commissioned} />
          </>
        ) : null}
      </dialog>
    </div>
  );
}
function ProofDetail({
  record: r,
  onClose,
  onSelect,
  events,
}: {
  record: Contribution;
  onClose: () => void;
  onSelect: (id: string) => void;
  events: Registry["events"];
}) {
  if (r.timeline_at)
    return <CatalogueDetail record={r} onClose={onClose} onSelect={onSelect} />;
  return (
    <section className="panel proof-detail">
      <div className="panel-heading">
        <button
          className="icon"
          aria-label="Close proof details"
          onClick={onClose}
        >
          <X size={17} />
        </button>
      </div>
      <div className="detail-body">
        <h2>{r.title}</h2>
        <p className="authors">{r.authors.map((a) => a.name).join(", ")}</p>
        <div className="exact-result">
          <span>EXACT θ</span>
          <strong>{boundLabel(r)}</strong>
          <code>≈ {decimal(r.theta, 32)}</code>
        </div>
        <h3>Method</h3>
        <p>{r.method}</p>
        <h3>Statement</h3>
        <pre>
          {theorem.replace(
            "θ",
            `(${r.theta.numerator} / ${r.theta.denominator} : ℝ)`,
          )}
        </pre>
        <h3>Provenance</h3>
        <dl>
          <dt>Submitted</dt>
          <dd>{timestamp(r.submitted_at)}</dd>
          <dt>First verified</dt>
          <dd>{timestamp(r.first_verified_at)}</dd>
          <dt>Merged</dt>
          <dd>{timestamp(r.merged_at)}</dd>
          <dt>Published</dt>
          <dd>{timestamp(r.published_at)}</dd>
          <dt>License</dt>
          <dd>{r.license}</dd>
        </dl>
        <span className="detail-label">SOURCE COMMIT</span>
        <code className="hash">{r.source_commit || "Not recorded"}</code>
        <span className="detail-label">ENTRYPOINT</span>
        <code className="hash">{r.entrypoint.declaration}</code>
        <div className="detail-links">
          <a
            href={`https://github.com/${r.repository}/tree/${r.source_commit}`}
            target="_blank"
            rel="noreferrer"
          >
            Pinned source <ExternalLink size={13} />
          </a>
          <a
            href={`https://github.com/${r.repository}/pull/${r.pr}`}
            target="_blank"
            rel="noreferrer"
          >
            Submission PR <ExternalLink size={13} />
          </a>
          <a href={publicUrl(r.receipt_url || "")}>
            Signed verification receipt
          </a>
          <a href={publicUrl(r.log_url || "")}>Complete checking logs</a>
        </div>
        <h3>Builds on</h3>
        {r.builds_on.length ? (
          r.builds_on.map((id) => (
            <button
              className="predecessor"
              key={id}
              onClick={() => onSelect(id)}
            >
              <GitBranch size={14} />
              {id}
            </button>
          ))
        ) : (
          <p className="muted">No explicit predecessors.</p>
        )}
        <h3>References</h3>
        {r.references.length ? (
          r.references.map((ref) => (
            <a
              className="reference"
              key={ref.url}
              href={ref.url}
              target="_blank"
              rel="noreferrer"
            >
              {ref.label} <ExternalLink size={13} />
            </a>
          ))
        ) : (
          <p className="muted">No references listed.</p>
        )}
        {events
          .filter((e) => e.id === r.id)
          .map((e, i) => (
            <p className="event-warning" key={i}>
              {e.type} · {e.reason}
            </p>
          ))}
      </div>
    </section>
  );
}
function Protocol({ commissioned }: { commissioned: boolean }) {
  return (
    <section className="protocol-grid">
      <article className="panel">
        <h2>Statement</h2>
        <p>The formal theorem to prove is:</p>
        <p>
          For every{" "}
          <MathJax inline>{String.raw`\(q\in\mathbb{N}_{>0}\)`}</MathJax>,{" "}
          <MathJax
            inline
          >{String.raw`\(\chi\in\widehat{(\mathbb{Z}/q\mathbb{Z})^\times}\)`}</MathJax>
          , <MathJax inline>{String.raw`\(s\in\mathbb{C}\)`}</MathJax> with{" "}
          <MathJax inline>{String.raw`\((\chi,s)\ne(1,1)\)`}</MathJax>,
        </p>
        <div className="statement-equation-row">
          <MathJax className="statement-equation">
            {String.raw`\(\operatorname{Re}(s)>\theta \;\Longrightarrow\; L(\chi,s)\ne 0\)`}
          </MathJax>
        </div>
        <p>
          Formulated in{" "}
          <a href="https://lean-lang.org/" target="_blank" rel="noreferrer">
            Lean
          </a>{" "}
          as:
        </p>
        <LeanCode
          code={leanTheorem}
          source={upstream + "ComparatorChallenges/DirichletSevenEighths.lean"}
        />
      </article>

      <article className="panel">
        <h2>Verification</h2>
        <h3>Requirements</h3>
        <p>
          Every result marked verified must pass Comparator’s statement,
          definition and axiom checks, followed by proof replay in Lean, NanoDa
          and con-ron. We use{" "}
          <a
            href="https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
            target="_blank"
            rel="noreferrer"
          >
            Palomar’s open-source proof checker
          </a>
          .
        </p>
        <p>
          {commissioned
            ? "Signed registry entries link to Comparator and NanoDa receipts and checking logs."
            : "Maintainers run these checks and publish the reports and exact checked statements with each result."}
        </p>
        <p>
          Only propext, Classical.choice and Quot.sound are allowed. These local
          checks are separate from Palomar registration and editorial review.
        </p>
        <h3>Labels</h3>
        <p>
          <strong>Verified in our framework:</strong> the result has passed all
          requirements above.
        </p>
        <p>
          <strong>Verification pending:</strong> the authors report a
          formalization that we have not independently reproduced. These results
          also contribute to the line.
        </p>
        <p>Each result links to its source and available checking logs.</p>
      </article>
      <article className="panel">
        <h2>Dates</h2>
        <p>
          Dates are in UTC and refer to publication, announcement or the first
          local Lean check. Hover over a publication date for its full
          timestamp. Verification dates are recorded separately in the result
          details.
        </p>
      </article>
    </section>
  );
}
