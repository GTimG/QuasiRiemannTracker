import {
  contributionDate,
  timelineRecords,
  verifiedHere,
} from "./catalogue.mjs";
import { BASELINE, cmp, frontierHistory, sub } from "./rational.mjs";

export function chartExtent(
  records,
  events = [],
  fullHistory = false,
  window = [0, 100],
  now = Date.now(),
) {
  const verified = records.filter(verifiedHere);
  const frontier = frontierHistory(timelineRecords(verified), events);
  const changes = frontier.filter(
    (point, index) =>
      point.theta &&
      cmp(point.theta, { numerator: "1", denominator: "1" }) < 0 &&
      (!frontier[index - 1]?.theta ||
        cmp(point.theta, frontier[index - 1].theta) !== 0),
  );
  const points = (rows) =>
    rows.map((record) => ({
      at: contributionDate(record),
      theta: record.theta,
    }));
  const fitted = fullHistory
    ? points(records)
    : changes.length
      ? changes
      : verified.length
        ? points(verified)
        : points(records);
  const times = [
    ...fitted.map((point) => Date.parse(point.at)),
    ...(fullHistory ? events.map((event) => Date.parse(event.at)) : []),
  ];
  const first = times.length ? Math.min(...times) : now;
  // Include the time of viewing, even when no new record has been submitted.
  const last = Math.max(now, times.length ? Math.max(...times) : now);
  const pad = Math.max((last - first) * 0.06, 86400000);
  const start = first - pad,
    end = last + pad;
  const visible = fitted.filter((point) => {
    const at = Date.parse(point.at);
    return (
      at >= start + ((end - start) * window[0]) / 100 &&
      at <= start + ((end - start) * window[1]) / 100
    );
  });
  const values = (visible.length ? visible : fitted)
    .map((point) => point.theta)
    .sort(cmp);
  let low = values[0] ?? { numerator: "0", denominator: "1" };
  let high = values.at(-1) ?? BASELINE;
  if (cmp(low, high) === 0) {
    low = sub(low, { numerator: "1", denominator: "1000000" });
    high = sub(high, { numerator: "-1", denominator: "1000000" });
  }
  return { start, end, low, high };
}
