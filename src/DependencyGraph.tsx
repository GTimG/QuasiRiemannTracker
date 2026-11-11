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
};
export type YAxis = "generation" | "bound";

// Bound axis: linear over the main range, compressed above an axis break.
const BOUND_SPAN = 1500,
  BREAK = 0.875;
const thetaOf = (r: Contribution) =>
  Number(r.theta.numerator) / Number(r.theta.denominator);

const LAYER = 46,
  SPREAD = 64,
  HEIGHT = 640,
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
  const directChildren = new Map<string, string[]>(
    records.map((r) => [r.id, []]),
  );
  for (const [id, ps] of direct)
    for (const p of ps) directChildren.get(p)!.push(id);

  const depth = new Map<string, number>();
  const generation = (id: string): number => {
    if (depth.has(id)) return depth.get(id)!;
    depth.set(id, 0);
    const d = Math.max(-1, ...parents.get(id)!.map(generation)) + 1;
    depth.set(id, d);
    return d;
  };
  const layers: string[][] = [];
  for (const r of [...records].sort((a, b) =>
    contributionDate(a).localeCompare(contributionDate(b)),
  ))
    (layers[generation(r.id)] ??= []).push(r.id);

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
  const pos = new Map<string, Point>();
  layers.forEach((ids, g) =>
    ids.forEach((id, i) =>
      pos.set(id, {
        x: (i - (ids.length - 1) / 2) * SPREAD,
        y: boundY
          ? boundY(thetaOf(byId.get(id)!))
          : g * LAYER + jitter(id) * 11,
      }),
    ),
  );
  // A small force relaxation: pull towards direct lineage, push neighbours apart.
  const ids = records.map((r) => r.id);
  for (let step = 0; step < 260; step++) {
    const cool = 1 - step / 260;
    const delta = new Map(ids.map((id) => [id, 0]));
    for (const id of ids) {
      const p = pos.get(id)!;
      const linked = [...direct.get(id)!, ...directChildren.get(id)!];
      for (const other of linked)
        delta.set(id, delta.get(id)! + (pos.get(other)!.x - p.x) * 0.035);
      delta.set(id, delta.get(id)! - p.x * 0.004);
      for (const other of ids) {
        if (other === id) continue;
        const q = pos.get(other)!;
        const dy = Math.abs(q.y - p.y);
        if (dy > LAYER * 1.4) continue;
        const dx = p.x - q.x || jitter(id + other);
        const near = SPREAD * (1.15 - dy / (LAYER * 1.4) / 2);
        if (Math.abs(dx) < near)
          delta.set(
            id,
            delta.get(id)! + Math.sign(dx) * (near - Math.abs(dx)) * 0.45,
          );
      }
    }
    for (const id of ids) pos.get(id)!.x += delta.get(id)! * cool;
  }
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
    bounds: {
      x0: Math.min(...xs),
      x1: Math.max(...xs),
      y0: Math.min(...ys),
      y1: Math.max(...ys),
    },
  };
}

type Box = { x0: number; y0: number; x1: number; y1: number };
const overlaps = (a: Box, b: Box) =>
  a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1;

export default function DependencyGraph({
  records,
  selected,
  onSelect,
  toolbar,
}: {
  records: Contribution[];
  selected: string | null;
  onSelect: (id: string) => void;
  toolbar?: React.ReactNode;
}) {
  const [axis, setAxis] = useState<YAxis>("generation");
  const graph = useMemo(() => layout(records, axis), [records, axis]);
  const byId = useMemo(() => new Map(records.map((r) => [r.id, r])), [records]);
  const frame = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState(900);
  const [view, setView] = useState<{ k: number; tx: number; ty: number }>();
  const [hover, setHover] = useState<string | null>(null);
  const [allEdges, setAllEdges] = useState(true);
  const drag = useRef<{ x: number; y: number; moved: boolean } | null>(null);

  const fit = (w = width) => {
    if (!records.length) return { k: 1, tx: 0, ty: 0 };
    const { x0, x1, y0, y1 } = graph.bounds;
    const k = Math.min(
      (w - Math.min(340, w * 0.45)) / Math.max(1, x1 - x0),
      (HEIGHT - 120) / Math.max(1, y1 - y0),
      1.6,
    );
    return {
      k,
      tx: w / 2 - ((x0 + x1) / 2) * k,
      ty: (w < 560 ? 96 : 52) - y0 * k,
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
      const k = Math.min(6, Math.max(0.25, c.k * factor));
      return {
        k,
        tx: cx - ((cx - c.tx) * k) / c.k,
        ty: cy - ((cy - c.ty) * k) / c.k,
      };
    });
  const screen = (id: string) => {
    const p = graph.pos.get(id)!;
    return { x: p.x * v.k + v.tx, y: p.y * v.k + v.ty };
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
      const text = short(c.title, c.id === focus ? 80 : 34);
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
  }, [records, v.k, v.tx, v.ty, width, focus, selected, allEdges]);

  return (
    <section className="panel dependency-graph" aria-label="Dependency graph">
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
              <text x={10} y={v.ty - 22 * v.k} className="axis-break">
                ≈
              </text>
            </g>
          )}
          <g className="edges">
            {edges.map(([from, to]) => {
              const a = screen(from),
                b = screen(to),
                my = (a.y + b.y) / 2;
              const on = lit?.has(from) && lit.has(to);
              return (
                <path
                  key={`${from}>${to}`}
                  className={on ? "on" : lit ? "dim" : undefined}
                  d={`M${a.x},${a.y} C${a.x},${my} ${b.x},${my} ${b.x},${b.y}`}
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
                onClick={() => setAxis(a)}
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
                onClick={() => setAllEdges(all)}
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
          <button aria-label="Zoom in" onClick={() => zoomAt(1.3)}>
            <Plus size={14} />
          </button>
          <button aria-label="Zoom out" onClick={() => zoomAt(1 / 1.3)}>
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
