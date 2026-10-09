import { useEffect, useMemo, useRef, useState } from "react";
import {
  Activity,
  Code2,
  ExternalLink,
  GitBranch,
  GitPullRequest,
  Info,
  Search,
  ShieldCheck,
  Table2,
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
  new Date(s).toISOString().replace("T", " ").replace(".000Z", " UTC");
const theorem = `∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},\n  (θ < s.re) → ¬ (χ = 1 ∧ s = 1) →\n  DirichletCharacter.LFunction χ s ≠ 0`;
export default function App() {
  const [registry, setRegistry] = useState<Registry>(initial),
    [catalogue, setCatalogue] = useState<Contribution[]>([]),
    [repository, setRepository] = useState<string | null>(null),
    [tab, setTab] = useState("Timeline"),
    [query, setQuery] = useState(""),
    [method, setMethod] = useState("all"),
    [sort, setSort] = useState("latest"),
    [status, setStatus] = useState("active"),
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
        .filter(
          (r) =>
            (status === "all" || !withdrawn.has(r.id)) &&
            (method === "all" ||
              (method === "record"
                ? r.is_record
                : method === "pending"
                  ? !verifiedHere(r)
                  : method === "verified"
                    ? verifiedHere(r)
                    : verifiedHere(r) && !r.is_record)) &&
            (!query ||
              `${r.title} ${r.id} ${r.method} ${r.authors.map((a) => a.name).join(" ")} ${boundLabel(r)}`
                .toLowerCase()
                .includes(query.toLowerCase())),
        )
        .sort((a, b) =>
          sort === "bound"
            ? cmp(a.theta, b.theta) ||
              contributionDate(a).localeCompare(contributionDate(b))
            : sort === "oldest"
              ? contributionDate(a).localeCompare(contributionDate(b))
              : contributionDate(b).localeCompare(contributionDate(a)),
        ),
    [all, status, method, query, sort, events],
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
      <aside className="sidebar">
        <a className="brand" href="#main" aria-label="QRH Bounds home">
          <span className="brand-symbol">
            q<span>↘</span>
          </span>
          <span>
            QRH<span>BOUNDS</span>
          </span>
        </a>
        <nav aria-label="Research views">
          {[
            { name: "Timeline", icon: Activity },
            { name: "Contributions", icon: Table2 },
            { name: "Protocol", icon: ShieldCheck },
          ].map(({ name, icon: Icon }) => (
            <button
              key={name}
              className={tab === name ? "nav-active" : ""}
              aria-current={tab === name ? "page" : undefined}
              onClick={() => setTab(name)}
            >
              <Icon size={18} />
              <span>{name}</span>
              {name === "Contributions" && <small>{all.length}</small>}
            </button>
          ))}
        </nav>
        <div className="sidebar-foot">
          <Code2 size={16} />
          <span>Apache 2.0</span>
        </div>
      </aside>
      <main id="main">
        <header className="topbar">
          <a href={publicUrl("proofs/qrh-20261009/source-public.tar.gz")}>
            Lean sources
          </a>
          <button className="button primary" onClick={() => setModal("submit")}>
            <GitPullRequest size={16} />
            Submit a proof
          </button>
        </header>
        <div className="content">
          <div className="page-title">
            <div>
              <h1>
                {tab === "Protocol" ? "Verification" : "Quasi-Riemann bounds"}
              </h1>
              {tab !== "Protocol" && best && (
                <p className="best-bound">
                  Best verified: θ ={" "}
                  <button onClick={() => setSelected(best.id)}>
                    {decimal(best.theta, 16)}
                  </button>
                </p>
              )}
            </div>
          </div>
          {error && (
            <div className="notice error" role="alert">
              {error}
            </div>
          )}
          {tab === "Protocol" ? (
            <Protocol commissioned={commissioned} />
          ) : (
            <>
              <div className="statement">
                <div>
                  <span className="theta-symbol">θ</span>
                  <span>
                    For every positive modulus q and complex Dirichlet character
                    χ,
                  </span>
                  <strong className="math">
                    Re(s) &gt; θ <span>⟹</span> L(χ, s) ≠ 0
                  </strong>
                  <small>excluding χ = 1 ∧ s = 1</small>
                </div>
                <button
                  className="icon"
                  aria-label="Read exact theorem"
                  onClick={() => setModal("policy")}
                >
                  <Info size={18} />
                </button>
              </div>
              <div className="filters">
                <div className="search">
                  <Search size={17} />
                  <input
                    aria-label="Search contributions"
                    placeholder="Search proofs, authors, methods…"
                    value={query}
                    onChange={(e) => setQuery(e.target.value)}
                  />
                  {query && (
                    <button
                      aria-label="Clear search"
                      onClick={() => setQuery("")}
                    >
                      <X size={14} />
                    </button>
                  )}
                </div>
                <select
                  aria-label="Contribution type"
                  value={method}
                  onChange={(e) => setMethod(e.target.value)}
                >
                  <option value="all">All contributions</option>
                  <option value="verified">Verified here</option>
                  <option value="pending">Verification pending</option>
                  <option value="record">Verified record improvements</option>
                  <option value="alternative">Alternative proofs</option>
                </select>
                {events.length > 0 && (
                  <select
                    aria-label="Historical status"
                    value={status}
                    onChange={(e) => setStatus(e.target.value)}
                  >
                    <option value="active">Active records</option>
                    <option value="all">Include withdrawn</option>
                  </select>
                )}
              </div>
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
                      <select
                        aria-label="Sort contributions"
                        value={sort}
                        onChange={(e) => setSort(e.target.value)}
                      >
                        <option value="latest">Newest result</option>
                        <option value="oldest">Oldest result</option>
                        <option value="bound">Smallest θ (exact)</option>
                      </select>
                    </div>
                    <div className="table-scroll">
                      <table>
                        <caption className="sr-only">
                          Equivalent keyboard-accessible table of every plotted
                          contribution
                        </caption>
                        <thead>
                          <tr>
                            <th>CONTRIBUTION / AUTHOR</th>
                            <th>EXACT BOUND θ</th>
                            <th>RESULT DATE</th>
                            <th>VERIFICATION</th>
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
                              <td>
                                <button
                                  className="row-title"
                                  onClick={() => setSelected(r.id)}
                                >
                                  {r.title}
                                </button>
                                <small>
                                  {r.authors.map((a) => a.name).join(", ")}
                                </small>
                              </td>
                              <td className="fraction-cell">
                                {boundLabel(r)}
                                <small>{decimal(r.theta, 14)}</small>
                              </td>
                              <td>
                                {date(contributionDate(r))}
                                <small>
                                  {r.date_label || "First verified"} · UTC
                                </small>
                              </td>
                              <td>
                                <span
                                  className={
                                    "tag " +
                                    (verifiedHere(r) ? "teal" : "amber")
                                  }
                                >
                                  {withdrawn.has(r.id)
                                    ? "Withdrawn"
                                    : statusLabel(r)}
                                </span>
                              </td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                    {!records.length && (
                      <div className="empty-table">
                        <FileCheck2 size={24} />
                        <h3>
                          {all.length
                            ? "No matching contributions"
                            : "No verified contributions yet"}
                        </h3>
                        <p>
                          {all.length
                            ? "Try another author, method or fraction."
                            : "Successful Lean and NanoDa checks, followed by attribution review, unlock publication."}
                        </p>
                        {all.length > 0 && (
                          <button
                            onClick={() => {
                              setQuery("");
                              setMethod("all");
                              setStatus("all");
                            }}
                          >
                            Reset filters
                          </button>
                        )}
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
          <footer>
            <span>QRH Bounds</span>
            <button onClick={() => setModal("policy")}>
              Verification details
            </button>
          </footer>
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
        <span className="eyebrow">PROOF DETAILS</span>
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
        <p>
          For every positive modulus q, complex Dirichlet character χ and
          complex s with Re(s) &gt; θ, L(χ, s) ≠ 0, excluding χ = 1 and s = 1. A
          smaller θ gives a stronger result.
        </p>
        <pre>{theorem}</pre>
        <a
          href={upstream + "ComparatorChallenges/DirichletSevenEighths.lean"}
          target="_blank"
          rel="noreferrer"
        >
          Upstream theorem specification <ExternalLink size={14} />
        </a>
      </article>
      <article className="panel">
        <h2>Verification labels</h2>
        <p>
          <strong>Verified in our framework:</strong> the result has passed all
          required proof checks listed below.
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
          local Lean check, as indicated in the table. Verification dates are
          recorded separately in the result details.
        </p>
      </article>
      <article className="panel">
        <h2>Required proof checks</h2>
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
      </article>
    </section>
  );
}
