import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import { Minus, Plus, Maximize2, Move, Info } from "lucide-react";
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
import {
  contributionDate,
  boundLabel,
  verifiedHere,
  statusLabel,
  timelineRecords,
} from "../core/catalogue.mjs";
export default function Chart({
  records,
  allRecords,
  events,
  selected,
  onSelect,
}: {
  records: Contribution[];
  allRecords: Contribution[];
  events: Event[];
  selected: string | null;
  onSelect: (r: Contribution) => void;
}) {
  const [window, setWindow] = useState<[number, number]>([0, 100]),
    [vertical, setVertical] = useState({ scale: 1, offset: 0 }),
    [hover, setHover] = useState<Contribution | null>(null);
  const dragging = useRef<{
    x: number;
    y: number;
    window: [number, number];
    offset: number;
  } | null>(null);
  const svg = useRef<SVGSVGElement>(null);
  const [W, setWidth] = useState(800);
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
  const times = [
      ...allRecords.map((r) => Date.parse(contributionDate(r))),
      ...events.map((e) => Date.parse(e.at)),
    ],
    minTime = times.length ? Math.min(...times) : Date.UTC(2026, 9, 1),
    maxTime = times.length ? Math.max(...times) : Date.UTC(2026, 9, 9),
    pad = Math.max((maxTime - minTime) * 0.06, 86400000);
  const domain: [number, number] = [minTime - pad, maxTime + pad];
  const span = domain[1] - domain[0],
    start = domain[0] + (span * window[0]) / 100,
    end = domain[0] + (span * window[1]) / 100;
  const inTime = allRecords.filter(
    (r) =>
      Date.parse(contributionDate(r)) >= start &&
      Date.parse(contributionDate(r)) <= end,
  );
  const values = inTime.map((r) => r.theta).sort(cmp);
  let low: Rational = values[0] ?? { numerator: "0", denominator: "1" },
    high: Rational = values.at(-1) ?? BASELINE;
  if (cmp(low, high) === 0) {
    low = sub(low, { numerator: "1", denominator: "1000000" });
    high = sub(high, { numerator: "-1", denominator: "1000000" });
  }
  const x = (at: string) =>
    L + ((Date.parse(at) - start) / (end - start)) * width;
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
  ) => {
    const span = window[1] - window[0],
      nextSpan = Math.max(0.0001, span * factor),
      anchor = window[0] + span * anchorX;
    setWindow([anchor - nextSpan * anchorX, anchor + nextSpan * (1 - anchorX)]);
    if (scaleVertical)
      setVertical((v) => {
        const scale = Math.max(0.0001, Math.min(1e6, v.scale / factor)),
          ratio = scale / v.scale;
        return {
          scale,
          offset: (1 - anchorY - 0.5) * (1 - ratio) + v.offset * ratio,
        };
      });
  };
  const fit = () => {
    setWindow([0, 100]);
    setVertical({ scale: 1, offset: 0 });
  };
  useEffect(() => {
    const element = svg.current;
    if (!element) return;
    const wheel = (event: WheelEvent) => {
      event.preventDefault();
      const bounds = element.getBoundingClientRect();
      if (event.deltaX) {
        const delta = (event.deltaX / width) * (window[1] - window[0]);
        setWindow([window[0] + delta, window[1] + delta]);
      }
      if (event.deltaY) {
        const unit =
          event.deltaMode === 1
            ? 16
            : event.deltaMode === 2
              ? bounds.height
              : 1;
        zoom(
          Math.exp(Math.max(-1, Math.min(1, event.deltaY * unit * 0.003))),
          Math.max(0, Math.min(1, (event.clientX - bounds.left - L) / width)),
          Math.max(0, Math.min(1, (event.clientY - bounds.top - T) / height)),
          !event.shiftKey,
        );
      }
    };
    element.addEventListener("wheel", wheel, { passive: false });
    return () => element.removeEventListener("wheel", wheel);
  }, [window, W]);
  const curve = useMemo(
    () => frontierHistory(timelineRecords(allRecords), events),
    [allRecords, events],
  );
  let path = "",
    connected = false;
  for (const p of curve) {
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
  if (connected) path += ` H ${W - R}`;
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
    return decimal(v, 8);
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
          <button className="icon" aria-label="Fit chart" onClick={fit}>
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
          aria-label="Interactive bound timeline. Plus and minus zoom; arrows pan; Home resets. Tab to select points."
          tabIndex={0}
          onKeyDown={(e) => {
            if (e.target !== e.currentTarget) return;
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
              zoom(0.7, 0.5, 0.5, !e.shiftKey);
            if (e.key === "-") zoom(1.4, 0.5, 0.5, !e.shiftKey);
            if (e.key === "Home") fit();
            if (e.key === "ArrowUp" || e.key === "ArrowDown")
              setVertical((v) => ({
                ...v,
                offset: v.offset + (e.key === "ArrowUp" ? 0.1 : -0.1),
              }));
            if (e.key === "ArrowLeft" || e.key === "ArrowRight") {
              const delta =
                (window[1] - window[0]) *
                0.1 *
                (e.key === "ArrowLeft" ? -1 : 1);
              setWindow([window[0] + delta, window[1] + delta]);
            }
          }}
          onPointerDown={(e) => {
            if ((e.target as Element).closest("[data-dot]")) return;
            dragging.current = {
              x: e.clientX,
              y: e.clientY,
              window,
              offset: vertical.offset,
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
            setWindow([d.window[0] - dx, d.window[1] - dx]);
            setVertical((v) => ({ ...v, offset: d.offset - dy }));
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
              >
                {allRecords.length ? tickLabel(t) : (0.9 - t * 0.4).toFixed(2)}
              </text>
              <text
                x={L + t * width}
                y={H - 18}
                textAnchor="middle"
                className="axis"
              >
                {new Date(start + t * (end - start)).toLocaleDateString(
                  "en-GB",
                  { day: "2-digit", month: "short", timeZone: "UTC" },
                )}
              </text>
            </g>
          ))}
          <text x={L} y={16} className="axis-label">
            {tiny ? "Offset from θ₀ · local scale" : "θ"}
          </text>
          <g clipPath="url(#plotClip)">
            {allRecords.length > 0 && (
              <path
                d={path}
                fill="none"
                stroke="#1d5d74"
                strokeWidth="2"
                strokeLinejoin="round"
              />
            )}
            {records.map((r) => {
              const px = x(contributionDate(r)),
                py = y(r.theta),
                label = labels[r.id];
              if (
                px < L - 6 ||
                px > W - R + 6 ||
                py < T - 10 ||
                py > H - B + 10
              )
                return null;
              return (
                <g
                  key={r.id}
                  data-dot
                  data-id={r.id}
                  data-time={Date.parse(contributionDate(r))}
                  role="button"
                  tabIndex={0}
                  aria-label={`Select ${r.title}, theta ${boundLabel(r)}`}
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
                    {contributionDate(r)}
                  </title>
                  <circle cx={px} cy={py} r={16} fill="transparent" />
                  {selected === r.id && (
                    <circle cx={px} cy={py} r={12} fill="#1d5d7422" />
                  )}
                  <circle
                    cx={px}
                    cy={py}
                    r={selected === r.id ? 6 : 5}
                    fill={
                      !verifiedHere(r)
                        ? "white"
                        : r.is_record
                          ? "#1d5d74"
                          : "#7184a2"
                    }
                    stroke={!verifiedHere(r) ? "#ad761e" : "white"}
                    strokeWidth={2}
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
          Best listed bound
        </span>
        <span>
          <i className="legend-dot pending-dot" />
          Verification pending
        </span>
        <span className="pan-hint">
          <Move size={13} />
          Drag to pan · scroll to zoom
        </span>
      </div>
      <p className="chart-note">
        <Info size={14} />
        <span>
          {tiny && <>Local axis origin θ₀ = {fraction(low)}. </>}
          Dates in UTC. The line includes results awaiting verification.
        </span>
      </p>
    </section>
  );
}
