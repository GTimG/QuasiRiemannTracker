import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import { Minus, Plus, Maximize2, Move, Search } from "lucide-react";
import { milestones } from "./bound-milestones";
import {
  BASELINE,
  sub,
  cmp,
  relativePosition,
  log10Rational,
  decimal,
  fraction,
  frontierHistory,
  reduced,
} from "../core/rational.mjs";
import type { Contribution, Event, Rational } from "./types";
import { chartExtent } from "../core/chart-viewport.mjs";
import type { GraphView, HistoryMode, UpdateGraph } from "./navigation";
import {
  contributionDate,
  formatContributionDate,
  boundLabel,
  verifiedHere,
  statusLabel,
  timelineRecords,
} from "../core/catalogue.mjs";

function zoomed(
  current: GraphView,
  factor: number,
  anchorX = 0.5,
  anchorY = 0.5,
  scaleVertical = true,
): GraphView {
  const span = current.window[1] - current.window[0];
  const nextSpan = Math.max(0.0001, Math.min(1e8, span * factor));
  const anchor = current.window[0] + span * anchorX;
  let vertical = current.vertical;
  if (scaleVertical) {
    const scale = Math.max(0.0001, Math.min(1e6, vertical.scale / factor));
    const ratio = scale / vertical.scale;
    vertical = {
      scale,
      offset: (1 - anchorY - 0.5) * (1 - ratio) + vertical.offset * ratio,
    };
  }
  return {
    ...current,
    window: [anchor - nextSpan * anchorX, anchor + nextSpan * (1 - anchorX)],
    vertical,
  };
}

export default function Chart({
  view,
  onViewChange,
  records,
  allRecords,
  events,
  selected,
  onSelect,
}: {
  view: GraphView;
  onViewChange: UpdateGraph;
  records: Contribution[];
  allRecords: Contribution[];
  events: Event[];
  selected: string | null;
  onSelect: (r: Contribution) => void;
}) {
  const { window, overview, vertical } = view;
  const [viewedAt] = useState(Date.now);
  const [hover, setHover] = useState<Contribution | null>(null);
  const lastWheel = useRef(0);
  const dragging = useRef<{
    x: number;
    y: number;
    window: [number, number];
    offset: number;
    moved: boolean;
  } | null>(null);
  const svg = useRef<SVGSVGElement>(null);
  const [W, setWidth] = useState(800);
  useEffect(() => {
    const endGesture = () => {
      lastWheel.current = 0;
      dragging.current = null;
    };
    globalThis.addEventListener("popstate", endGesture);
    return () => globalThis.removeEventListener("popstate", endGesture);
  }, []);
  useEffect(() => {
    const el = svg.current?.parentElement;
    if (!el) return;
    const observer = new ResizeObserver(([entry]) =>
      setWidth(Math.max(280, entry.contentRect.width)),
    );
    observer.observe(el);
    return () => observer.disconnect();
  }, []);
  const H = 355,
    L = 112,
    R = 24,
    T = 35,
    B = 60;
  const width = W - L - R,
    height = H - T - B;
  const extent = useMemo(
    () => chartExtent(allRecords, events, overview, window, viewedAt),
    [allRecords, events, overview, window, viewedAt],
  );
  const low = overview ? { numerator: "1", denominator: "2" } : extent.low;
  const high = overview ? { numerator: "1", denominator: "1" } : extent.high;
  const span = extent.end - extent.start,
    start = extent.start + (span * window[0]) / 100,
    end = extent.start + (span * window[1]) / 100;
  const x = (at: string | number) =>
    L +
    (((typeof at === "number" ? at : Date.parse(at)) - start) / (end - start)) *
      width;
  const y = (v: Rational) => {
    const ratio = relativePosition(v, low, high);
    return (
      T +
      height *
        (1 - ((ratio - 0.5) * 0.83 * vertical.scale + 0.5 + vertical.offset))
    );
  };
  const zoom = (
    factor: number,
    anchorX = 0.5,
    anchorY = 0.5,
    scaleVertical = true,
    history: HistoryMode = "push",
  ) => {
    lastWheel.current = 0;
    onViewChange(
      (current) => zoomed(current, factor, anchorX, anchorY, scaleVertical),
      history,
    );
  };
  const fit = (overview: boolean) => {
    lastWheel.current = 0;
    onViewChange(() => ({
      overview,
      window: [0, 100],
      vertical: { scale: 1, offset: 0 },
    }));
  };
  const fitLeaderboard = () => fit(false);
  const fitMilestones = () => fit(true);
  const pointRadius = overview ? Math.min(5, 2 * Math.sqrt(vertical.scale)) : 5;
  // SVG paints later elements on top. Keep every filled frontier point above
  // hollow alternatives, independently of the leaderboard's sort order.
  const plottedRecords = [...records].sort(
    (a, b) => Number(Boolean(a.is_record)) - Number(Boolean(b.is_record)),
  );
  useEffect(() => {
    const element = svg.current;
    if (!element) return;
    const wheel = (event: WheelEvent) => {
      event.preventDefault();
      if (!event.deltaX && !event.deltaY) return;
      const bounds = element.getBoundingClientRect();
      const now = Date.now();
      const history = now - lastWheel.current < 400 ? "replace" : "push";
      lastWheel.current = now;
      onViewChange((current) => {
        const delta =
          (event.deltaX / width) * (current.window[1] - current.window[0]);
        const panned: GraphView = {
          ...current,
          window: [current.window[0] + delta, current.window[1] + delta],
        };
        if (!event.deltaY) return panned;
        const unit =
          event.deltaMode === 1
            ? 16
            : event.deltaMode === 2
              ? bounds.height
              : 1;
        return zoomed(
          panned,
          Math.exp(Math.max(-1, Math.min(1, event.deltaY * unit * 0.003))),
          Math.max(0, Math.min(1, (event.clientX - bounds.left - L) / width)),
          Math.max(0, Math.min(1, (event.clientY - bounds.top - T) / height)),
          !event.shiftKey,
        );
      }, history);
    };
    element.addEventListener("wheel", wheel, { passive: false });
    return () => element.removeEventListener("wheel", wheel);
  }, [W, onViewChange]);
  const curve = useMemo(
    () =>
      frontierHistory(timelineRecords(allRecords.filter(verifiedHere)), events),
    [allRecords, events],
  );
  let path = "",
    connected = false;
  for (const p of curve) {
    if (Date.parse(p.at) > viewedAt) break;
    const px = x(p.at);
    if (!p.theta) {
      if (connected) path += ` H ${px}`;
      connected = false;
      continue;
    }
    const py = y(p.theta);
    path += connected ? ` H ${px} V ${py}` : `M ${px} ${py}`;
    connected = true;
  }
  // The empty area to the right is padding, not a prediction of future records.
  if (connected) path += ` H ${x(viewedAt)}`;
  const tiny =
    cmp(sub(high, low), { numerator: "1", denominator: "100000000" }) < 0;
  const tickValue = (t: number) => {
    const ratio = (1 - t - 0.5 - vertical.offset) / vertical.scale / 0.83 + 0.5;
    const k = BigInt(Math.round(ratio * 1e9));
    const span = sub(high, low);
    const delta = reduced(
      BigInt(span.numerator) * k,
      BigInt(span.denominator) * 1000000000n,
    );
    return sub(low, {
      numerator: String(-BigInt(delta.numerator)),
      denominator: delta.denominator,
    });
  };
  const tickLabel = (t: number) => {
    const v = tiny ? sub(tickValue(t), low) : tickValue(t);
    if (tiny) {
      if (v.numerator === "0") return "0";
      const n = BigInt(v.numerator);
      const abs = {
        numerator: String(n < 0n ? -n : n),
        denominator: v.denominator,
      };
      const l = log10Rational(abs),
        exp = Math.floor(l);
      return `${n < 0n ? "-" : ""}${(10 ** (l - exp)).toFixed(1)}e${exp}`;
    }
    return overview
      ? Number(decimal(v, 4).replace("…", "")).toFixed(2)
      : decimal(v, 8);
  };
  // Measure actual SVG text so labels respect both neighbouring names and the
  // plot edges. Keep the newest label when a dense cluster has no free space.
  const [labels, setLabels] = useState<
    Record<
      string,
      { x: number; y: number; lineX: number; lineY: number; moved: boolean }
    >
  >({});
  useLayoutEffect(() => {
    const points = Array.from(
      svg.current?.querySelectorAll<SVGGElement>("[data-dot]") ?? [],
    ).map((el) => {
      const circle = el.querySelector("circle")!;
      return {
        id: el.dataset.id!,
        at: Number(el.dataset.time),
        x: Number(circle.getAttribute("cx")),
        y: Number(circle.getAttribute("cy")),
        text: el.querySelector<SVGTextElement>(".point-label"),
      };
    });
    const placed: { x: number; y: number; width: number; height: number }[] =
      [];
    const next: typeof labels = {};
    const overlaps = (a: (typeof placed)[number], b: (typeof placed)[number]) =>
      a.x < b.x + b.width + 6 &&
      a.x + a.width + 6 > b.x &&
      a.y < b.y + b.height + 6 &&
      a.y + a.height + 6 > b.y;
    for (const point of points.sort(
      (a, b) => b.at - a.at || a.id.localeCompare(b.id),
    )) {
      if (!point.text) continue;
      const box = point.text.getBBox();
      if (!box.width || !box.height || box.width > width) continue;
      const baselineOffset = box.y - Number(point.text.getAttribute("y"));
      const right = Math.max(L, Math.min(point.x + 10, W - R - box.width));
      const centered = Math.max(
        L,
        Math.min(point.x - box.width / 2, W - R - box.width),
      );
      const left = Math.max(
        L,
        Math.min(point.x - 10 - box.width, W - R - box.width),
      );
      const above = point.y - 10 - box.height;
      const below = point.y + 10;
      // Center lower labels directly beneath their dots.
      for (const [lx, ly] of [
        [right, above],
        [centered, below],
        [left, above],
      ]) {
        const rect = { x: lx, y: ly, width: box.width, height: box.height };
        if (
          ly < T - 10 ||
          ly + box.height > H - B + 8 ||
          placed.some((other) => overlaps(rect, other)) ||
          points.some((p) =>
            overlaps(rect, { x: p.x - 3, y: p.y - 3, width: 6, height: 6 }),
          )
        )
          continue;
        next[point.id] = {
          x: lx,
          y: ly - baselineOffset,
          lineX: Math.max(lx, Math.min(point.x, lx + box.width)),
          lineY: ly > point.y ? ly - 2 : ly + box.height + 2,
          moved: lx !== point.x + 10 || ly !== above,
        };
        placed.push(rect);
        break;
      }
    }
    setLabels((previous) =>
      JSON.stringify(previous) === JSON.stringify(next) ? previous : next,
    );
  }, [
    records,
    W,
    start,
    end,
    low.numerator,
    low.denominator,
    high.numerator,
    high.denominator,
    vertical.scale,
    vertical.offset,
  ]);
  const ticks = [0, 0.25, 0.5, 0.75, 1];
  return (
    <section className="panel chart-panel" aria-label="Bound progress">
      <div className="chart-toolbar">
        <div className="chart-tools">
          <button
            className="icon"
            aria-label="Zoom in"
            onClick={() => zoom(0.7)}
          >
            <Plus size={17} />
          </button>
          <button
            className="icon"
            aria-label="Zoom out"
            onClick={() => zoom(1.4)}
          >
            <Minus size={17} />
          </button>
          <button
            className="icon"
            aria-label="Fit leaderboard"
            title="Fit leaderboard bounds"
            onClick={fitLeaderboard}
          >
            <Search size={16} />
          </button>
          <button
            className="icon"
            aria-label="Fit ½–1"
            title="Fit full range: ½–1"
            onClick={fitMilestones}
          >
            <Maximize2 size={16} />
          </button>
        </div>
      </div>
      <div className="chart-wrap">
        <svg
          ref={svg}
          viewBox={`0 0 ${W} ${H}`}
          className="chart"
          role="group"
          aria-label="Interactive bound timeline. Plus and minus zoom; arrows pan; Home fits leaderboard bounds. Tab to select points."
          tabIndex={0}
          onKeyDown={(e) => {
            if (e.target !== e.currentTarget) return;
            lastWheel.current = 0;
            if (
              [
                "+",
                "=",
                "-",
                "Home",
                "ArrowLeft",
                "ArrowRight",
                "ArrowUp",
                "ArrowDown",
              ].includes(e.key)
            )
              e.preventDefault();
            if (e.key === "+" || e.key === "=")
              zoom(0.7, 0.5, 0.5, !e.shiftKey, e.repeat ? "replace" : "push");
            if (e.key === "-")
              zoom(1.4, 0.5, 0.5, !e.shiftKey, e.repeat ? "replace" : "push");
            if (e.key === "Home") fitLeaderboard();
            if (e.key === "ArrowUp" || e.key === "ArrowDown")
              onViewChange(
                (current) => ({
                  ...current,
                  vertical: {
                    ...current.vertical,
                    offset:
                      current.vertical.offset +
                      (e.key === "ArrowUp" ? 0.1 : -0.1),
                  },
                }),
                e.repeat ? "replace" : "push",
              );
            if (e.key === "ArrowLeft" || e.key === "ArrowRight") {
              const delta =
                (window[1] - window[0]) *
                0.1 *
                (e.key === "ArrowLeft" ? -1 : 1);
              onViewChange(
                (current) => ({
                  ...current,
                  window: [
                    current.window[0] + delta,
                    current.window[1] + delta,
                  ],
                }),
                e.repeat ? "replace" : "push",
              );
            }
          }}
          onPointerDown={(e) => {
            if ((e.target as Element).closest("[data-dot]")) return;
            dragging.current = {
              x: e.clientX,
              y: e.clientY,
              window,
              offset: vertical.offset,
              moved: false,
            };
            e.currentTarget.setPointerCapture(e.pointerId);
          }}
          onPointerUp={() => {
            dragging.current = null;
          }}
          onPointerCancel={() => {
            dragging.current = null;
          }}
          onPointerMove={(e) => {
            if (!dragging.current) return;
            const d = dragging.current,
              bounds = e.currentTarget.getBoundingClientRect(),
              dx =
                ((e.clientX - d.x) / bounds.width) *
                (d.window[1] - d.window[0]),
              dy = (e.clientY - d.y) / bounds.height;
            if (!dx && !dy && !d.moved) return;
            lastWheel.current = 0;
            onViewChange(
              (current) => ({
                ...current,
                window: [d.window[0] - dx, d.window[1] - dx],
                vertical: { ...current.vertical, offset: d.offset - dy },
              }),
              d.moved ? "replace" : "push",
            );
            d.moved = true;
          }}
        >
          <defs>
            <clipPath id="plotClip">
              <rect
                x={L - 8}
                y={T - 15}
                width={width + 16}
                height={height + 25}
              />
            </clipPath>
          </defs>
          {ticks.map((t) => (
            <g key={t}>
              <line
                x1={L}
                x2={W - R}
                y1={T + t * height}
                y2={T + t * height}
                stroke="#e1e7ea"
              />
              <text
                x={L - 14}
                y={T + t * height + 4}
                textAnchor="end"
                className="axis"
                data-axis="bound"
              >
                {allRecords.length || overview
                  ? tickLabel(t)
                  : (0.9 - t * 0.4).toFixed(2)}
              </text>
              <text
                x={L + t * width}
                y={H - 18}
                textAnchor="middle"
                className="axis"
                data-axis="date"
              >
                {new Date(start + t * (end - start)).toLocaleDateString(
                  "en-GB",
                  end - start > 365.25 * 86400000
                    ? { year: "numeric", timeZone: "UTC" }
                    : { day: "2-digit", month: "short", timeZone: "UTC" },
                )}
              </text>
            </g>
          ))}
          <text x={L} y={16} className="axis-label">
            {tiny ? "Offset from θ₀ · local scale" : "θ"}
          </text>
          <g clipPath="url(#plotClip)">
            {milestones.map((m) => (
              <line
                key={m.id}
                data-milestone={m.id}
                x1={L}
                x2={W - R}
                y1={y(m.theta)}
                y2={y(m.theta)}
                stroke="#82959e"
                strokeWidth={1.5}
                strokeDasharray={m.dashed ? "7 5" : undefined}
              >
                <title>
                  {m.label} · {m.title}
                </title>
              </line>
            ))}
            {allRecords.length > 0 && (
              <path
                className="verified-frontier"
                d={path}
                fill="none"
                stroke="#1d5d74"
                strokeWidth="2"
                strokeLinejoin="round"
              />
            )}
            {plottedRecords.map((r) => {
              const px = x(contributionDate(r)),
                py = y(r.theta),
                label = labels[r.id];
              const inView =
                px >= L - 6 &&
                px <= W - R + 6 &&
                py >= T - 10 &&
                py <= H - B + 10;
              return (
                <g
                  key={r.id}
                  data-dot
                  aria-hidden={!inView}
                  data-id={r.id}
                  data-time={Date.parse(contributionDate(r))}
                  role="button"
                  tabIndex={inView ? 0 : -1}
                  aria-label={`Select ${r.title}, theta ${boundLabel(r)}`}
                  aria-description={
                    r.is_record
                      ? "On the verified frontier"
                      : "Outside the verified frontier"
                  }
                  aria-pressed={selected === r.id}
                  onKeyDown={(e) => {
                    if (e.key === "Enter" || e.key === " ") {
                      e.preventDefault();
                      onSelect(r);
                    }
                  }}
                  onClick={() => onSelect(r)}
                  onFocus={() => setHover(r)}
                  onBlur={() => setHover(null)}
                  onMouseEnter={() => setHover(r)}
                  onMouseLeave={() => setHover(null)}
                  className="dot"
                >
                  <title>
                    {r.title} · {boundLabel(r)} ·{" "}
                    {r.authors.map((a) => a.name).join(", ")} ·{" "}
                    {formatContributionDate(r)}
                  </title>
                  <circle cx={px} cy={py} r={16} fill="transparent" />
                  {selected === r.id && (
                    <circle
                      cx={px}
                      cy={py}
                      r={pointRadius + 7}
                      fill="#1d5d7422"
                    />
                  )}
                  <circle
                    cx={px}
                    cy={py}
                    r={pointRadius + (selected === r.id ? 1 : 0)}
                    fill={r.is_record ? "#1d5d74" : "white"}
                    stroke={!verifiedHere(r) ? "#ad761e" : "#1d5d74"}
                    strokeWidth={overview ? 1 : 2}
                  />
                  {W > 600 &&
                    (r.timeline_at || cmp(r.theta, BASELINE) === 0) && (
                      <>
                        {label?.moved && (
                          <line
                            x1={px}
                            y1={py + (label.lineY > py ? 7 : -7)}
                            x2={label.lineX}
                            y2={label.lineY}
                            stroke="#9caeb9"
                            strokeWidth={1}
                            pointerEvents="none"
                          />
                        )}
                        <text
                          x={label?.x ?? px + 10}
                          y={label?.y ?? py - 13}
                          visibility={label ? "visible" : "hidden"}
                          className="point-label"
                        >
                          {r.title.split(" · ")[0]}
                        </text>
                      </>
                    )}
                </g>
              );
            })}
          </g>
          {milestones.map((m) => {
            const py = y(m.theta);
            return py >= T && py <= H - B ? (
              <text
                key={m.id}
                x={L + 6}
                y={py - 7}
                textAnchor="start"
                className="milestone-label"
              >
                {m.label}
              </text>
            ) : null;
          })}
        </svg>
        {!allRecords.length && (
          <div className="chart-empty">
            <span className="empty-mark">∅</span>
            <h3>No results to display.</h3>
          </div>
        )}
        {hover && (
          <div className="chart-tooltip" role="status">
            <strong>{hover.title}</strong>
            <span>
              θ = {boundLabel(hover)} ·{" "}
              {hover.authors.map((a) => a.name).join(", ")}
            </span>
            <small>{statusLabel(hover)}</small>
          </div>
        )}
      </div>
      <div className="chart-bottom">
        <span>
          <i className="legend-line" />
          Best verified bound
        </span>
        <span className="pan-hint">
          <Move size={13} />
          Drag to pan · scroll to zoom
        </span>
      </div>
      {tiny && (
        <p className="chart-note">Local axis origin θ₀ = {fraction(low)}.</p>
      )}
    </section>
  );
}
