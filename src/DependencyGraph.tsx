import { useEffect, useMemo, useRef, useState } from "react";
import { Maximize2, Minus, Plus } from "lucide-react";
import { decimal } from "../core/rational.mjs";
import { contributionDate } from "../core/catalogue.mjs";
import type { Contribution } from "./types";

type Point = { x: number; y: number };
type Layout = {
  pos: Map<string, Point>;
  radius: Map<string, number>;
  parents: Map<string, string[]>;
  direct: Map<string, string[]>;
  lineage: (id: string) => Set<string>;
  bounds: { x0: number; x1: number; y0: number; y1: number };
  ticks: { y: number; label: string }[];
  dateTicks: { x: number; label: string }[];
};
export type YAxis = "generation" | "bound";

// Bound axis: linear over the main range, compressed above an axis break.
const BOUND_SPAN = 1500,
  BREAK = 0.875;
const thetaOf = (r: Contribution) =>
  Number(r.theta.numerator) / Number(r.theta.denominator);

const LAYER = 46,
  DEFAULT_HEIGHT = 640,
  FONT = 11.5,
  CHAR = 6.1;

const short = (s: string, n: number) =>
  s.length > n ? s.slice(0, n - 1) + "…" : s;

/** Deterministic pseudo-random jitter so the layout is stable between renders. */
const jitter = (id: string) => {
  let h = 2166136261;
  for (const c of id) h = Math.imul(h ^ c.charCodeAt(0), 16777619);
  return ((h >>> 0) / 2 ** 32 - 0.5) * 2;
};

// Horizontal spacing between consecutive submissions.
const TIME_STEP = 34;

function layout(records: Contribution[], axis: YAxis): Layout {
  const byId = new Map(records.map((r) => [r.id, r]));
  const parents = new Map(
    records.map((r) => [r.id, r.builds_on.filter((p) => byId.has(p))]),
  );
  const children = new Map<string, string[]>(records.map((r) => [r.id, []]));
  for (const [id, ps] of parents) for (const p of ps) children.get(p)!.push(id);

  const closure = (start: string, next: Map<string, string[]>) => {
    const out = new Set<string>();
    const walk = (id: string) => {
      for (const n of next.get(id) ?? [])
        if (!out.has(n)) {
          out.add(n);
          walk(n);
        }
    };
    walk(start);
    return out;
  };
  const ancestors = new Map(records.map((r) => [r.id, closure(r.id, parents)]));
  const descendants = new Map(
    records.map((r) => [r.id, closure(r.id, children)]),
  );
  // Transitive reduction: drop A→C when A→B→…→C already exists.
  const direct = new Map(
    [...parents].map(([id, ps]) => [
      id,
      ps.filter((p) => !ps.some((q) => q !== p && ancestors.get(q)!.has(p))),
    ]),
  );

  const depth = new Map<string, number>();
  const generation = (id: string): number => {
    if (depth.has(id)) return depth.get(id)!;
    depth.set(id, 0);
    const d = Math.max(-1, ...parents.get(id)!.map(generation)) + 1;
    depth.set(id, d);
    return d;
  };
  const best = Math.min(...records.map(thetaOf));
  const boundY =
    axis === "bound"
      ? (t: number) =>
          t <= BREAK
            ? ((BREAK - t) / (BREAK - best)) * BOUND_SPAN
            : -40 - Math.log10(1 + (t - BREAK) * 1e3) * 40
      : null;
  const ticks: Layout["ticks"] = [];
  if (boundY) {
    const step = 0.0002;
    for (let t = BREAK; t - best > step / 3; t -= step)
      ticks.push({ y: boundY(t), label: t.toFixed(4) });
    ticks.push({ y: boundY(best), label: best.toFixed(6) });
    for (const t of new Set(records.map(thetaOf).filter((t) => t > BREAK)))
      ticks.push({ y: boundY(t), label: String(+t.toFixed(4)) });
  }
  // x is submission order, evenly spaced (a date scale would let 1922 dominate).
  const order = [...records].sort((a, b) =>
    contributionDate(a).localeCompare(contributionDate(b)),
  );
  const rank = new Map(order.map((r, i) => [r.id, i]));
  const dateTicks: Layout["dateTicks"] = [];
  {
    let last = "";
    order.forEach((r, i) => {
      const day = new Date(contributionDate(r)).toLocaleDateString("en-GB", {
        day: "2-digit",
        month: "short",
        year: i === 0 ? "numeric" : undefined,
        timeZone: "UTC",
      });
      if (
        day !== last &&
        (!dateTicks.length ||
          i * TIME_STEP - dateTicks.at(-1)!.x >= TIME_STEP * 5)
      )
        dateTicks.push({ x: i * TIME_STEP, label: day });
      last = day;
    });
  }
  const pos = new Map<string, Point>(
    order.map((r, i) => [
      r.id,
      {
        x: i * TIME_STEP,
        y: boundY
          ? boundY(thetaOf(r))
          : generation(r.id) * LAYER + jitter(r.id) * 11,
      },
    ]),
  );
  const ids = records.map((r) => r.id);
  const radius = new Map(
    ids.map((id) => [id, 3.2 + 1.9 * Math.sqrt(descendants.get(id)!.size)]),
  );
  const xs = ids.map((id) => pos.get(id)!.x),
    ys = ids.map((id) => pos.get(id)!.y);
  return {
    pos,
    radius,
    parents,
    direct,
    lineage: (id) =>
      new Set([id, ...ancestors.get(id)!, ...descendants.get(id)!]),
    ticks,
    dateTicks,
    bounds: {
      x0: Math.min(...xs),
      x1: Math.max(...xs),
      y0: Math.min(...ys),
      y1: Math.max(...ys),
    },
  };
}

// x is submission order, so it is fitted independently of y (ax = x/y scale).
type View = { k: number; ax: number; tx: number; ty: number };

type Box = { x0: number; y0: number; x1: number; y1: number };
const overlaps = (a: Box, b: Box) =>
  a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1;

export default function DependencyGraph({
  records,
  selected,
  onSelect,
  toolbar,
  axis,
  allEdges,
  onAxis,
  onAllEdges,
  height: HEIGHT = DEFAULT_HEIGHT,
  label = "Dependency graph",
}: {
  records: Contribution[];
  selected: string | null;
  onSelect: (id: string) => void;
  toolbar?: React.ReactNode;
  axis: YAxis;
  allEdges: boolean;
  onAxis: (axis: YAxis) => void;
  onAllEdges: (all: boolean) => void;
  height?: number;
  label?: string;
}) {
  const graph = useMemo(() => layout(records, axis), [records, axis]);
  const byId = useMemo(() => new Map(records.map((r) => [r.id, r])), [records]);
  const frame = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState(900);
  const [view, setView] = useState<View>();
  const [hover, setHover] = useState<string | null>(null);
  const drag = useRef<{ x: number; y: number; moved: boolean } | null>(null);

  const fit = (w = width) => {
    if (!records.length) return { k: 1, ax: 1, tx: 0, ty: 0 };
    const { x0, x1, y0, y1 } = graph.bounds;
    // Narrow screens wrap the toolbar and footer, so leave more room.
    const top = w < 560 ? 96 : 52,
      bottom = w < 560 ? 104 : 68;
    const k = Math.min((HEIGHT - top - bottom) / Math.max(1, y1 - y0), 1.6);
    const kx = Math.min(
      (w - Math.min(340, w * 0.45)) / Math.max(1, x1 - x0),
      2.5,
    );
    return {
      k,
      ax: kx / k,
      tx: w / 2 - ((x0 + x1) / 2) * kx,
      ty: top - y0 * k,
    };
  };
  useEffect(() => {
    const el = frame.current;
    if (!el) return;
    setView(undefined);
    const observer = new ResizeObserver(([entry]) =>
      setWidth(entry.contentRect.width),
    );
    observer.observe(el);
    return () => observer.disconnect();
  }, [graph]);
  useEffect(() => {
    const el = frame.current;
    if (!el) return;
    const wheel = (e: WheelEvent) => {
      e.preventDefault();
      const rect = el.getBoundingClientRect();
      zoomAt(
        Math.exp(-e.deltaY * 0.0015),
        e.clientX - rect.left,
        e.clientY - rect.top,
      );
    };
    el.addEventListener("wheel", wheel, { passive: false });
    return () => el.removeEventListener("wheel", wheel);
  });
  const v = view ?? fit();
  const zoomAt = (factor: number, cx = width / 2, cy = HEIGHT / 2) =>
    setView((current) => {
      const c = current ?? fit();
      const k = Math.min(6, Math.max(0.05, c.k * factor));
      return {
        k,
        ax: c.ax,
        tx: cx - ((cx - c.tx) * k) / c.k,
        ty: cy - ((cy - c.ty) * k) / c.k,
      };
    });
  const dateY = HEIGHT - (width < 560 ? 64 : 32);
  // Thin date labels so they stay at least ~64px apart on screen.
  const shownDates: { x: number; label: string }[] = [];
  for (const t of graph.dateTicks.map((t) => ({
    ...t,
    x: t.x * v.k * v.ax + v.tx,
  })))
    if (!shownDates.length || t.x - shownDates.at(-1)!.x >= 64)
      shownDates.push(t);
  const screen = (id: string) => {
    const p = graph.pos.get(id)!;
    return { x: p.x * v.k * v.ax + v.tx, y: p.y * v.k + v.ty };
  };
  const r = (id: string) => graph.radius.get(id)! * Math.sqrt(v.k);

  const focus = hover ?? selected;
  const lit = focus && byId.has(focus) ? graph.lineage(focus) : null;
  const edges = records.flatMap((c) =>
    (allEdges ? graph.parents : graph.direct)
      .get(c.id)!
      .map((p) => [p, c.id] as const),
  );

  // Greedy label placement, most important first, like the frontier chart.
  const labels = useMemo(() => {
    const placed: Box[] = records.map((c) => {
      const p = screen(c.id),
        rr = r(c.id);
      return { x0: p.x - rr, y0: p.y - rr, x1: p.x + rr, y1: p.y + rr };
    });
    // Keep labels clear of the axes, the date row and the toolbar.
    const narrow = width < 560;
    if (graph.ticks.length) placed.push({ x0: 0, x1: 60, y0: 0, y1: HEIGHT });
    placed.push({ x0: 0, x1: width, y0: dateY - 12, y1: HEIGHT });
    placed.push(
      narrow
        ? { x0: 0, x1: width, y0: 0, y1: 92 }
        : { x0: width - 340, x1: width, y0: 0, y1: 48 },
    );
    // Phones get fewer, shorter labels; hovering still names any node.
    const maxLabels = narrow ? 6 : Infinity;
    const priority = (c: Contribution) =>
      (c.id === focus ? 1e6 : 0) +
      (c.id === selected ? 1e5 : 0) +
      (lit?.has(c.id) ? 1e4 : 0) +
      (c.is_record ? 1e3 : 0) +
      graph.radius.get(c.id)!;
    const out: {
      id: string;
      x: number;
      y: number;
      anchor: "start" | "end";
      text: string;
    }[] = [];
    for (const c of [...records].sort((a, b) => priority(b) - priority(a))) {
      if (lit && !lit.has(c.id)) continue;
      const p = screen(c.id),
        rr = r(c.id) + 5;
      if (c.id !== focus && out.length >= maxLabels) continue;
      const text = short(
        c.title,
        c.id === focus ? (narrow ? 40 : 80) : narrow ? 22 : 34,
      );
      const w = text.length * CHAR,
        h = FONT + 3;
      const options = [
        { x: p.x + rr, y: p.y, anchor: "start" as const },
        { x: p.x - rr, y: p.y, anchor: "end" as const },
        { x: p.x + rr - 4, y: p.y - rr - 3, anchor: "start" as const },
        { x: p.x + rr - 4, y: p.y + rr + 5, anchor: "start" as const },
      ];
      for (const o of options) {
        const x0 = o.anchor === "start" ? o.x : o.x - w;
        const box = { x0, x1: x0 + w, y0: o.y - h / 2, y1: o.y + h / 2 };
        if (
          box.x0 < 2 ||
          box.x1 > width - 2 ||
          box.y0 < 2 ||
          box.y1 > HEIGHT - 26
        )
          continue;
        if (c.id !== focus && placed.some((b) => overlaps(b, box))) continue;
        placed.push(box);
        out.push({ id: c.id, ...o, text });
        break;
      }
    }
    return out;
  }, [graph, v.k, v.ax, v.tx, v.ty, width, HEIGHT, focus, selected]);

  return (
    <section className="panel dependency-graph" aria-label={label}>
      <div
        ref={frame}
        className="graph-frame"
        style={{ height: HEIGHT }}
        onPointerDown={(e) => {
          drag.current = { x: e.clientX, y: e.clientY, moved: false };
        }}
        onPointerMove={(e) => {
          const d = drag.current;
          if (!d || !e.buttons) return;
          const dx = e.clientX - d.x,
            dy = e.clientY - d.y;
          if (!d.moved && Math.hypot(dx, dy) < 3) return;
          if (!d.moved)
            (e.currentTarget as Element).setPointerCapture(e.pointerId);
          d.moved = true;
          d.x = e.clientX;
          d.y = e.clientY;
          setView({ ...v, tx: v.tx + dx, ty: v.ty + dy });
        }}
        onPointerUp={() => setTimeout(() => (drag.current = null))}
      >
        <svg
          width={width}
          height={HEIGHT}
          role="group"
          aria-label="Submissions arranged by what they build on"
        >
          {graph.ticks.length > 0 && (
            <g className="ticks" aria-hidden="true">
              {graph.ticks.map((t) => {
                const y = t.y * v.k + v.ty;
                return (
                  <g key={t.label}>
                    <line x1={58} x2={width} y1={y} y2={y} />
                    <text x={52} y={y} dy="0.35em" textAnchor="end">
                      {t.label}
                    </text>
                  </g>
                );
              })}
            </g>
          )}
          {graph.dateTicks.length > 0 && (
            <g className="ticks" aria-hidden="true">
              {shownDates.map((t) => {
                const x = t.x;
                return (
                  <g key={t.label}>
                    <line x1={x} x2={x} y1={0} y2={dateY - 12} />
                    <text x={x} y={dateY} textAnchor="middle">
                      {t.label}
                    </text>
                  </g>
                );
              })}
            </g>
          )}
          <g className="edges">
            {edges.map(([from, to]) => {
              const a = screen(from),
                b = screen(to),
                mx = (a.x + b.x) / 2;
              const on = lit?.has(from) && lit.has(to);
              return (
                <path
                  key={`${from}>${to}`}
                  className={on ? "on" : lit ? "dim" : undefined}
                  d={`M${a.x},${a.y} C${mx},${a.y} ${mx},${b.y} ${b.x},${b.y}`}
                />
              );
            })}
          </g>
          <g className="labels" aria-hidden="true">
            {labels.map((l) => (
              <text
                key={l.id}
                x={l.x}
                y={l.y}
                dy="0.35em"
                textAnchor={l.anchor}
                className={l.id === focus ? "focus" : undefined}
              >
                {l.text}
              </text>
            ))}
          </g>
          {records.map((c) => {
            const p = screen(c.id);
            const kind = c.is_record ? " record" : "";
            return (
              <circle
                key={c.id}
                data-node={c.id}
                cx={p.x}
                cy={p.y}
                r={r(c.id)}
                className={`node${kind}${c.id === selected ? " selected" : ""}${
                  lit && !lit.has(c.id) ? " dim" : ""
                }`}
                tabIndex={0}
                role="button"
                aria-label={`${c.title}, θ ≤ ${decimal(c.theta, 8)}`}
                onMouseEnter={() => setHover(c.id)}
                onMouseLeave={() => setHover(null)}
                onFocus={() => setHover(c.id)}
                onBlur={() => setHover(null)}
                onClick={() => !drag.current?.moved && onSelect(c.id)}
                onKeyDown={(e) => e.key === "Enter" && onSelect(c.id)}
              >
                <title>
                  {`${c.title}\n${c.authors.map((a) => a.name).join(", ")}\nθ ≤ ${decimal(c.theta, 12)}`}
                </title>
              </circle>
            );
          })}
        </svg>
        <div className="graph-tools" role="toolbar" aria-label="Graph options">
          <div className="mode-switch" role="group" aria-label="Vertical axis">
            {(["generation", "bound"] as const).map((a) => (
              <button
                key={a}
                aria-pressed={axis === a}
                onClick={() => onAxis(a)}
              >
                {a === "generation" ? "Generations" : "Bound θ"}
              </button>
            ))}
          </div>
          <div className="mode-switch" role="group" aria-label="Edges">
            {([false, true] as const).map((all) => (
              <button
                key={String(all)}
                aria-pressed={allEdges === all}
                onClick={() => onAllEdges(all)}
              >
                {all ? "All edges" : "Direct"}
              </button>
            ))}
          </div>
          {toolbar}
        </div>
        <div className="graph-footer">
          <span className="graph-legend">
            <span>
              <i className="record" /> New best bound
            </span>
            <span>
              <i /> Other
            </span>
          </span>
          <span>
            {records.length} submissions · {edges.length} dependencies
          </span>
        </div>
        <div className="graph-controls">
          <button aria-label="Zoom graph in" onClick={() => zoomAt(1.3)}>
            <Plus size={14} />
          </button>
          <button aria-label="Zoom graph out" onClick={() => zoomAt(1 / 1.3)}>
            <Minus size={14} />
          </button>
          <button aria-label="Fit graph" onClick={() => setView(fit())}>
            <Maximize2 size={13} />
          </button>
        </div>
      </div>
    </section>
  );
}
