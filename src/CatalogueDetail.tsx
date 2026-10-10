import { X, ExternalLink, GitBranch } from "lucide-react";
import { boundLabel, verifiedHere, statusLabel } from "../core/catalogue.mjs";
import { decimal } from "../core/rational.mjs";
import type { Contribution } from "./types";
import { publicUrl } from "./urls";

export default function CatalogueDetail({
  record: r,
  onClose,
  onSelect,
}: {
  record: Contribution;
  onClose: () => void;
  onSelect: (id: string) => void;
}) {
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
        <span className={`tag ${verifiedHere(r) ? "teal" : "amber"}`}>
          {statusLabel(r)}
        </span>
        <div className="exact-result">
          <span>EXACT θ</span>
          <strong>{boundLabel(r)}</strong>
          <code>≈ {decimal(r.theta, 18)}</code>
        </div>
        {r.exact_bound && (
          <p className="muted">
            The algebraic expression is the exact bound. A certified rational
            enclosure is used only to position its dot.
          </p>
        )}
        <h3>Verification in this project</h3>
        <p>{r.verification_note}</p>
        <h3>Method</h3>
        <p>{r.method}</p>
        {r.attribution_note && (
          <>
            <h3>Credits</h3>
            <p>{r.attribution_note}</p>
          </>
        )}
        <h3>Dates & provenance</h3>
        <dl>
          <dt>{r.date_label}</dt>
          <dd>{r.timeline_at?.slice(0, 10)} (UTC)</dd>
          <dt>Verified here</dt>
          <dd>
            {r.first_verified_at
              ? r.first_verified_at.replace("T", " ").replace("Z", " UTC")
              : "Pending"}
          </dd>
          <dt>License</dt>
          <dd>{r.license}</dd>
        </dl>
        {r.source_commit && (
          <>
            <span className="detail-label">PINNED SOURCE COMMIT</span>
            <code className="hash">{r.source_commit}</code>
          </>
        )}
        {r.entrypoint.declaration && (
          <>
            <span className="detail-label">THEOREM DECLARATION</span>
            <code className="hash">{r.entrypoint.declaration}</code>
          </>
        )}
        <h3>Sources & downloads</h3>
        {r.references
          .filter(
            (ref) =>
              !(ref.url.endsWith(".lean") && /statement/i.test(ref.label)),
          )
          .map((ref) => (
            <a
              className="reference"
              key={ref.url}
              href={publicUrl(ref.url)}
              target="_blank"
              rel="noreferrer"
            >
              {ref.label}
              <ExternalLink size={13} />
            </a>
          ))}
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
          <p className="muted">Baseline contribution.</p>
        )}
      </div>
    </section>
  );
}
