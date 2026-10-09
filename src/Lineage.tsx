import { useState } from "react";
import { Maximize2, Minus, Plus, GitBranch } from "lucide-react";
import type { Contribution } from "./types";
import {
  contributionDate,
  boundLabel,
  verifiedHere,
} from "../core/catalogue.mjs";
export default function Lineage({
  records,
  selected,
  onSelect,
}: {
  records: Contribution[];
  selected: string | null;
  onSelect: (r: Contribution) => void;
}) {
  const [zoom, setZoom] = useState(1),
    [ancestry, setAncestry] = useState(false),
    [offset, setOffset] = useState(0);
  const ordered = [...records].sort((a, b) =>
    contributionDate(a).localeCompare(contributionDate(b)),
  );
  const width = Math.max(900, ordered.length * 180),
    pos = new Map(
      ordered.map((r, i) => [r.id, { x: 100 + i * 165, y: 70 + (i % 3) * 95 }]),
    );
  const relevant = new Set<string>();
  function parents(id: string) {
    if (relevant.has(id)) return;
    relevant.add(id);
    records.find((r) => r.id === id)?.builds_on.forEach(parents);
  }
  if (selected) parents(selected);
  return (
    <section className="panel lineage">
      <div className="panel-heading">
        <div>
          <span className="eyebrow">MATHEMATICAL REUSE</span>
          <h2>Contribution lineage</h2>
        </div>
        <div className="chart-tools">
          <label className="check">
            <input
              type="checkbox"
              checked={ancestry}
              onChange={(e) => setAncestry(e.target.checked)}
            />
            Selected ancestry
          </label>
          <button
            className="icon"
            aria-label="Zoom lineage in"
            onClick={() => setZoom((v) => Math.min(4, v * 1.3))}
          >
            <Plus size={17} />
          </button>
          <button
            className="icon"
            aria-label="Zoom lineage out"
            onClick={() => setZoom((v) => Math.max(0.5, v / 1.3))}
          >
            <Minus size={17} />
          </button>
          <button
            className="icon"
            aria-label="Fit lineage"
            onClick={() => {
              setZoom(1);
              setOffset(0);
            }}
          >
            <Maximize2 size={16} />
          </button>
        </div>
      </div>
      {records.length ? (
        <>
          <svg
            viewBox={`${offset} 0 ${width / zoom} 355`}
            aria-label="Contribution lineage graph. Arrows move the view; buttons inspect contributions."
            tabIndex={0}
            onKeyDown={(e) => {
              if (e.key === "ArrowRight") {
                setOffset((v) => v + 100);
                e.preventDefault();
              }
              if (e.key === "ArrowLeft") {
                setOffset((v) => v - 100);
                e.preventDefault();
              }
            }}
          >
            <defs>
              <marker
                id="arrow"
                markerWidth="7"
                markerHeight="7"
                refX="6"
                refY="3"
                orient="auto"
              >
                <path d="M0 0L6 3L0 6" fill="none" stroke="#758ca3" />
              </marker>
            </defs>
            {ordered.flatMap((r) =>
              r.builds_on.map((id) => {
                const a = pos.get(id),
                  b = pos.get(r.id);
                return a &&
                  b &&
                  (!ancestry ||
                    !selected ||
                    (relevant.has(r.id) && relevant.has(id))) ? (
                  <path
                    key={id + r.id}
                    d={`M ${a.x + 8} ${a.y} C ${a.x + 70} ${a.y},${b.x - 70} ${b.y},${b.x - 10} ${b.y}`}
                    fill="none"
                    stroke="#a4b6c7"
                    strokeWidth="2"
                    markerEnd="url(#arrow)"
                  />
                ) : null;
              }),
            )}
            {ordered.map((r) => {
              const p = pos.get(r.id)!;
              return (
                <g
                  key={r.id}
                  role="button"
                  tabIndex={0}
                  aria-label={`Inspect lineage ${r.title}`}
                  opacity={
                    ancestry && selected && !relevant.has(r.id) ? 0.25 : 1
                  }
                  onClick={() => onSelect(r)}
                  onKeyDown={(e) => {
                    if (["Enter", " "].includes(e.key)) {
                      onSelect(r);
                      e.preventDefault();
                    }
                  }}
                  className="lineage-node"
                >
                  <circle
                    cx={p.x}
                    cy={p.y}
                    r={selected === r.id ? 12 : 8}
                    fill={
                      !verifiedHere(r)
                        ? "white"
                        : selected === r.id
                          ? "#148d80"
                          : "#49637c"
                    }
                    stroke={!verifiedHere(r) ? "#ad761e" : "none"}
                    strokeWidth={2}
                  />
                  <text x={p.x} y={p.y + 32} textAnchor="middle">
                    {boundLabel(r)}
                  </text>
                  <text
                    x={p.x}
                    y={p.y + 51}
                    className="axis"
                    textAnchor="middle"
                  >
                    {r.id}
                  </text>
                </g>
              );
            })}
          </svg>
          <label className="lineage-pan">
            Pan graph
            <input
              aria-label="Pan lineage"
              type="range"
              min={-100}
              max={width}
              value={offset}
              onChange={(e) => setOffset(+e.target.value)}
            />
          </label>
        </>
      ) : (
        <div className="empty-table">
          <GitBranch />
          <p>
            Verified contributions and their declared predecessors will appear
            here.
          </p>
        </div>
      )}
      <p className="chart-note">
        Edges come only from explicit builds_on IDs. Bibliographic references
        and similar methods do not create edges.
      </p>
    </section>
  );
}
