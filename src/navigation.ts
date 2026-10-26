import { useSyncExternalStore } from "react";

export const tabs = [
  "Timeline",
  "Leaderboard",
  "Milestones",
  "Protocol",
] as const;
export type Tab = (typeof tabs)[number];
export type GraphView = {
  overview: boolean;
  window: [number, number];
  vertical: { scale: number; offset: number };
};
export type HistoryMode = "push" | "replace";
export type UpdateGraph = (
  update: (current: GraphView) => GraphView,
  history?: HistoryMode,
) => void;
type View = { tab: Tab; graph: GraphView };

const defaultGraph = (): GraphView => ({
  overview: false,
  window: [0, 100],
  vertical: { scale: 1, offset: 0 },
});

function pair(value: string | null): [number, number] | null {
  if (!value) return null;
  const parts = value.split(",");
  if (parts.length !== 2 || parts.some((part) => !part.trim())) return null;
  const numbers = parts.map(Number);
  return numbers.every(Number.isFinite) ? [numbers[0], numbers[1]] : null;
}

function readView(url: URL): View {
  const params = url.searchParams;
  const graph = defaultGraph();
  graph.overview = params.get("view") === "overview";
  const x = pair(params.get("x")),
    y = pair(params.get("y"));
  if (
    x &&
    x.every((value) => Math.abs(value) <= 1e8) &&
    x[1] - x[0] >= 0.000099999 &&
    x[1] - x[0] <= 1e8
  )
    graph.window = x;
  if (y && y[0] >= 0.0001 && y[0] <= 1e6 && Math.abs(y[1]) <= 1e6)
    graph.vertical = { scale: y[0], offset: y[1] };
  return {
    tab:
      tabs.find((tab) => tab.toLowerCase() === params.get("tab")) ?? "Timeline",
    graph,
  };
}

function viewUrl(view: View, href = window.location.href) {
  const url = new URL(href);
  url.searchParams.set("tab", view.tab.toLowerCase());
  url.searchParams.set(
    "view",
    view.graph.overview ? "overview" : "leaderboard",
  );
  const { window: x, vertical: y } = view.graph;
  if (x[0] === 0 && x[1] === 100) url.searchParams.delete("x");
  else url.searchParams.set("x", x.join(","));
  if (y.scale === 1 && y.offset === 0) url.searchParams.delete("y");
  else url.searchParams.set("y", `${y.scale},${y.offset}`);
  return url;
}

const navigationEvent = "qrh:navigation";
function writeView(view: View, mode: HistoryMode) {
  const url = viewUrl(view);
  if (url.href === window.location.href) return;
  window.history[mode === "push" ? "pushState" : "replaceState"](
    window.history.state,
    "",
    url,
  );
  window.dispatchEvent(new Event(navigationEvent));
}
function subscribe(notify: () => void) {
  window.addEventListener("popstate", notify);
  window.addEventListener("hashchange", notify);
  window.addEventListener(navigationEvent, notify);
  return () => {
    window.removeEventListener("popstate", notify);
    window.removeEventListener("hashchange", notify);
    window.removeEventListener(navigationEvent, notify);
  };
}
const snapshot = () => window.location.href;
const setTab = (tab: Tab) =>
  writeView({ ...readView(new URL(snapshot())), tab }, "push");
const setGraph: UpdateGraph = (update, mode = "push") => {
  const current = readView(new URL(snapshot()));
  const next = { ...current, graph: update(current.graph) };
  // Apply the same finite viewport limits to interactions and incoming links.
  writeView(readView(viewUrl(next)), mode);
};

export function useNavigation() {
  const href = useSyncExternalStore(subscribe, snapshot);
  const view = readView(new URL(href));
  return {
    ...view,
    setTab,
    setGraph,
    tabHref: (tab: Tab) => viewUrl({ ...view, tab }, href).href,
  };
}
