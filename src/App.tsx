import {
  useEffect,
  useMemo,
  useRef,
  useState,
  useSyncExternalStore,
} from "react";
import { MathJax } from "better-react-mathjax";
import { Github, GitPullRequest, X } from "lucide-react";
import Chart from "./Chart";
import { cmp, decimal, recordHistory } from "../core/rational.mjs";
import type { Contribution } from "./types";
import {
  contributionDate,
  verifiedHere,
  timelineRecords,
  historicalBaseline,
} from "../core/catalogue.mjs";
import { publicUrl } from "./urls";
import Leaderboard, { type SortKey } from "./Leaderboard";
import Contributors from "./Contributors";
import { contributorLeaderboard } from "../core/contributors.mjs";
import Milestones from "./Milestones";
import DependencyGraph from "./DependencyGraph";
import CatalogueDetail from "./CatalogueDetail";
import LeanCode from "./LeanCode";
import { tabs, useNavigation, type Tab } from "./navigation";
const upstream =
  "https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/";
const leanTheorem = `theorem quasi_riemann_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (θ : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    LFunction χ s ≠ 0 := by
  sorry`;
// Side-by-side front page layout; matches the .front-row breakpoint.
const wideQuery = "(min-width: 1000px)";
const subscribeWide = (notify: () => void) => {
  const query = window.matchMedia(wideQuery);
  query.addEventListener("change", notify);
  return () => query.removeEventListener("change", notify);
};
const isWide = () => window.matchMedia(wideQuery).matches;

export default function App() {
  const wide = useSyncExternalStore(subscribeWide, isWide);
  const ancestryBox = useRef<HTMLElement>(null);
  const [ancestryHeight, setAncestryHeight] = useState<number>();
  const {
    tab,
    graph,
    submissions,
    setTab,
    setGraph,
    setSubmissionView,
    tabHref,
  } = useNavigation();
  const mode = submissions.mode;
  const navigate = (event: React.MouseEvent<HTMLAnchorElement>, next: Tab) => {
    if (
      event.button ||
      event.metaKey ||
      event.ctrlKey ||
      event.shiftKey ||
      event.altKey
    )
      return;
    event.preventDefault();
    setTab(next);
  };
  const [catalogue, setCatalogue] = useState<Contribution[]>([]),
    [repository, setRepository] = useState<string | null>(null),
    [sort, setSort] = useState<{
      key: SortKey;
      direction: "ascending" | "descending";
    }>({ key: "bound", direction: "ascending" }),
    [selected, setSelected] = useState<string | null>(() =>
      window.location.hash.startsWith("#entry-")
        ? decodeURIComponent(window.location.hash.slice(7))
        : null,
    ),
    [error, setError] = useState(""),
    [modal, setModal] = useState<"submit" | "policy" | null>(null),
    [ancestryAxis, setAncestryAxis] = useState<"bound" | "generation">("bound"),
    [ancestryEdges, setAncestryEdges] = useState(true);
  const dialog = useRef<HTMLDialogElement>(null);
  useEffect(() => {
    const read = (name: string) =>
      fetch(publicUrl(name)).then((r) => {
        if (!r.ok) throw Error(`Could not load ${name}`);
        return r.json();
      });
    Promise.all([read("catalogue.json"), read("site.json")])
      .then(([c, config]) => {
        if (c.schema_version !== 1 || !Array.isArray(c.records))
          throw Error("Unsupported research data.");
        setCatalogue(c.records);
        setRepository(config.repository);
      })
      .catch((e) => setError(e.message));
  }, []);
  useEffect(() => {
    if (modal && !dialog.current?.open) dialog.current?.showModal();
    if (!modal && dialog.current?.open) dialog.current?.close();
  }, [modal]);
  const ranked = new Map(
    recordHistory(timelineRecords(catalogue.filter(verifiedHere))).map((r) => [
      r.id,
      r.is_record,
    ]),
  );
  const all = catalogue.map((r) => ({
    ...r,
    is_record: ranked.get(r.id) === true,
  }));
  const records = useMemo(
    () =>
      [...all].sort((a, b) => {
        const comparison =
          sort.key === "bound"
            ? cmp(a.theta, b.theta)
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
    [all, sort],
  );
  const active = all,
    best = [...active]
      .filter(verifiedHere)
      .sort((a, b) => cmp(a.theta, b.theta))[0];
  // The best verified submission together with everything it builds on.
  const ancestry = useMemo(() => {
    if (!best) return [];
    const byId = new Map(all.map((r) => [r.id, r]));
    const keep = new Set<string>();
    const walk = (id: string) => {
      if (keep.has(id) || !byId.has(id)) return;
      keep.add(id);
      byId.get(id)!.builds_on.forEach(walk);
    };
    walk(best.id);
    return all.filter((r) => keep.has(r.id));
  }, [all, best]);
  // The front-page contributor box is as tall as the ancestry graph beside it.
  useEffect(() => {
    const el = ancestryBox.current;
    if (!el) return;
    const observer = new ResizeObserver(() =>
      setAncestryHeight(el.offsetHeight),
    );
    observer.observe(el);
    return () => observer.disconnect();
  }, [tab, best?.id]);
  const revealRecord = (id: string) => {
    // Opens in whichever view (graph or list) the user last chose.
    setTab("Submissions");
    setSelected(id);
    requestAnimationFrame(() =>
      (
        document.getElementById(`entry-${id}`) ??
        document.querySelector(".graph-detail")
      )?.scrollIntoView({ block: "nearest", behavior: "smooth" }),
    );
  };
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
            revealRecord(r.id);
            await new Promise(requestAnimationFrame);
            return { id: r.id, theta: r.theta };
          },
        },
        { signal: controller.signal },
      ),
    ).catch(() => {});
    return () => controller.abort();
  }, [all]);
  const modeSwitch = (
    <div className="mode-switch" role="group" aria-label="Submission view">
      {(["list", "graph"] as const).map((m) => (
        <button
          key={m}
          aria-pressed={mode === m}
          onClick={() => setSubmissionView({ mode: m })}
        >
          {m === "list" ? "List" : "Graph"}
        </button>
      ))}
    </div>
  );
  return (
    <div className="shell">
      <main id="main">
        <header className="topbar">
          <a
            className="brand"
            href={tabHref("Timeline")}
            onClick={(event) => navigate(event, "Timeline")}
          >
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
                  onClick={() => revealRecord(best.id)}
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
            {tabs.map((name) => (
              <a
                key={name}
                href={tabHref(name)}
                aria-current={tab === name ? "page" : undefined}
                onClick={(event) => navigate(event, name)}
              >
                {name}
                {name === "Submissions" && <small>{all.length}</small>}
                {name === "Contributors" && (
                  <small>{contributorLeaderboard(all).length}</small>
                )}
              </a>
            ))}
          </nav>
          {error && (
            <div className="notice error" role="alert">
              {error}
            </div>
          )}
          {tab === "Protocol" ? (
            <Protocol />
          ) : tab === "Milestones" ? (
            <Milestones />
          ) : (
            <>
              <div className="research-layout">
                <div className="research-main">
                  {tab === "Timeline" && (
                    <Chart
                      title="Best achieved bound"
                      view={graph}
                      onViewChange={setGraph}
                      events={[]}
                      records={records.filter(
                        (record) =>
                          verifiedHere(record) || historicalBaseline(record),
                      )}
                      allRecords={all.filter(
                        (record) =>
                          verifiedHere(record) || historicalBaseline(record),
                      )}
                      selected={selected}
                      onSelect={(r) => revealRecord(r.id)}
                    />
                  )}{" "}
                  {tab === "Timeline" ? (
                    <div className="front-row">
                      <Contributors
                        records={all}
                        onSelect={revealRecord}
                        submissionsHref={tabHref("Submissions")}
                        // Desktop: as tall as the graph, scrolling inside.
                        // Phones: top 5, so the page scrolls normally.
                        height={wide ? ancestryHeight : undefined}
                        limit={wide ? undefined : 5}
                        seeAll={{
                          href: tabHref("Contributors"),
                          onClick: (event) => navigate(event, "Contributors"),
                        }}
                      />
                      {best && (
                        <section
                          ref={ancestryBox}
                          className="ancestry"
                          aria-labelledby="ancestry-title"
                        >
                          <div className="section-title">
                            <strong id="ancestry-title">
                              Ancestry graph of best submission
                            </strong>
                            <a
                              className="see-all"
                              href={tabHref("Submissions")}
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
                                setTab("Submissions");
                                setSubmissionView({ mode: "graph" }, "replace");
                              }}
                            >
                              See all
                            </a>
                          </div>
                          <DependencyGraph
                            label="Ancestry graph of best submission"
                            records={ancestry}
                            selected={selected}
                            onSelect={revealRecord}
                            height={460}
                            axis={ancestryAxis}
                            allEdges={ancestryEdges}
                            onAxis={setAncestryAxis}
                            onAllEdges={setAncestryEdges}
                          />
                        </section>
                      )}
                    </div>
                  ) : tab === "Contributors" ? (
                    <Contributors
                      records={all}
                      onSelect={revealRecord}
                      submissionsHref={tabHref("Submissions")}
                    />
                  ) : (
                    <>
                      {mode === "graph" ? (
                        <>
                          <DependencyGraph
                            records={all}
                            selected={selected}
                            onSelect={setSelected}
                            toolbar={modeSwitch}
                            axis={submissions.axis}
                            allEdges={submissions.edges === "all"}
                            onAxis={(axis) => setSubmissionView({ axis })}
                            onAllEdges={(all) =>
                              setSubmissionView({
                                edges: all ? "all" : "direct",
                              })
                            }
                          />
                          {selected && all.some((r) => r.id === selected) && (
                            <div className="panel graph-detail">
                              <CatalogueDetail
                                record={all.find((r) => r.id === selected)!}
                                onClose={() => setSelected(null)}
                                onSelect={setSelected}
                              />
                            </div>
                          )}
                        </>
                      ) : (
                        <Leaderboard
                          records={records}
                          selected={selected}
                          onSelect={setSelected}
                          onNavigate={revealRecord}
                          sort={sort}
                          onSort={setSort}
                          toolbar={modeSwitch}
                        />
                      )}
                    </>
                  )}
                </div>
              </div>
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
              Open a GitHub pull request with your Lean proof and exact bound.
            </p>
            <ol className="guide-list">
              <li>
                Add{" "}
                <code>
                  submissions/YYYY-MM-DD-&lt;slug&gt;/src/Candidate/Main.lean
                </code>{" "}
                with theorem <code>Candidate.bound</code>. Use the PR’s original
                creation date in UTC only once, at the start of the directory,
                and keep it for later updates.
              </li>
              <li>
                Start the PR body with QRH-Result, QRH-Bound and QRH-Decimal.
                For a new submission, QRH-Result is the slug without the date
                prefix; existing submissions keep their stable IDs and Lean
                namespaces. Add metadata.json beside the Lean source with the
                result title, authors and description. Proof checks run
                automatically, including on drafts.
              </li>
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
              Every result on the website has passed the project’s verification
              checks.
            </p>
          </>
        ) : modal === "policy" ? (
          <>
            <h2>Verification details</h2>
            <Protocol />
          </>
        ) : null}
      </dialog>
    </div>
  );
}
function Protocol() {
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
          Every result on the website has passed Comparator’s statement,
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
          Verification runs through the project’s GitHub Actions CI. If CI
          resources run out, maintainers may run the same verification checks on
          maintainer infrastructure. Results are verified before merging and
          link to their committed source and any recorded verification report.
        </p>
        <p>
          The permitted axioms are propext, Classical.choice and Quot.sound.
        </p>
        <h3>Labels</h3>
        <p>
          <strong>Verified in our framework:</strong> the result has passed all
          requirements above.
        </p>
        <p>Verification records link to the checker run or archived report.</p>
      </article>
      <article className="panel">
        <h2>Dates</h2>
        <p>
          Every result has a public announcement date with source evidence.
          Opening a public submission PR supplies that date when no earlier
          announcement is documented. Dates are in UTC; hover for the recorded
          timestamp. When only a day or year is known, the precision is stated
          without implying an exact time. PR submission and verification dates
          appear separately in the result details. Commit timestamps document
          the source history; they do not establish when a commit was first
          pushed publicly or mathematical priority.
        </p>
      </article>
    </section>
  );
}
