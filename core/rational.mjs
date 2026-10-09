// Exact rationals are decimal integer strings at every persistence boundary.
const integer = /^(0|-?[1-9][0-9]{0,199})$/;
const positive = /^[1-9][0-9]{0,199}$/;
export function gcd(a, b) {
  a = a < 0n ? -a : a;
  while (b) {
    [a, b] = [b, a % b];
  }
  return a;
}
export function rational(numerator, denominator) {
  if (
    typeof numerator !== "string" ||
    typeof denominator !== "string" ||
    !integer.test(numerator) ||
    !positive.test(denominator)
  )
    throw Error(
      "Use canonical integer strings and a positive denominator (maximum 200 digits).",
    );
  const n = BigInt(numerator),
    d = BigInt(denominator);
  if (gcd(n, d) !== 1n) throw Error("Rational must be normalized.");
  return { numerator, denominator };
}
export function reduced(n, d) {
  if (d <= 0n) throw Error("Positive denominator required");
  const g = gcd(n, d);
  return { numerator: String(n / g), denominator: String(d / g) };
}
export function cmp(a, b) {
  const k =
    BigInt(a.numerator) * BigInt(b.denominator) -
    BigInt(b.numerator) * BigInt(a.denominator);
  return k < 0n ? -1 : k > 0n ? 1 : 0;
}
export function sub(a, b) {
  return reduced(
    BigInt(a.numerator) * BigInt(b.denominator) -
      BigInt(b.numerator) * BigInt(a.denominator),
    BigInt(a.denominator) * BigInt(b.denominator),
  );
}
export const BASELINE = Object.freeze({ numerator: "7", denominator: "8" });
export function fraction(a) {
  return `${a.numerator}/${a.denominator}`;
}
export function decimal(a, digits = 18) {
  let n = BigInt(a.numerator),
    d = BigInt(a.denominator);
  const sign = n < 0n ? "-" : "";
  n = n < 0n ? -n : n;
  let out = sign + String(n / d),
    r = n % d;
  if (!r) return out;
  out += ".";
  for (let i = 0; i < digits && r; i++) {
    r *= 10n;
    out += String(r / d);
    r %= d;
  }
  return out + (r ? "…" : "");
}
// Ratios/differences are computed exactly BEFORE conversion; tiny improvements survive cancellation.
export function relativePosition(value, low, high) {
  const v = sub(value, low),
    s = sub(high, low);
  if (s.numerator === "0") return 0.5;
  const scaled =
    (BigInt(v.numerator) * BigInt(s.denominator) * 10n ** 18n) /
    (BigInt(v.denominator) * BigInt(s.numerator));
  const limit = 10n ** 24n;
  return (
    Number(scaled > limit ? limit : scaled < -limit ? -limit : scaled) / 1e18
  );
}
export function log10Rational(a) {
  if (BigInt(a.numerator) <= 0n) throw Error("Log needs positive improvement");
  const logInt = (s) =>
    Math.log10(Number(s.slice(0, 16))) + s.length - Math.min(s.length, 16);
  return logInt(a.numerator) - logInt(a.denominator);
}
export function recordHistory(records, events = []) {
  const active = new Map();
  const result = [];
  const stream = [
    ...records.map((r) => ({
      at: r.first_verified_at,
      type: "verify",
      record: r,
    })),
    ...events,
  ].sort(
    (a, b) =>
      a.at.localeCompare(b.at) ||
      (a.type === "verify" && b.type === "verify"
        ? a.record.id.localeCompare(b.record.id)
        : a.type === "verify"
          ? -1
          : 1),
  );
  for (const e of stream) {
    if (e.type === "verify") {
      const r = e.record;
      const best = [...active.values()].sort(cmp)[0] ?? null;
      const improvement = best === null || cmp(r.theta, best) < 0;
      active.set(r.id, r.theta);
      result.push({
        ...r,
        is_record: improvement,
        record_theta: improvement ? r.theta : best,
      });
    } else active.delete(e.id);
  }
  return result;
}
export function activeRecords(records, events) {
  const removed = new Set(
    events
      .filter((e) => ["withdraw", "supersede"].includes(e.type))
      .map((e) => e.id),
  );
  return records.filter((r) => !removed.has(r.id));
}
// Retains historical records; withdrawals change the active frontier from the event time onward.
export function frontierHistory(records, events) {
  const stream = [
    ...records.map((r) => ({
      at: r.first_verified_at,
      type: "verify",
      record: r,
    })),
    ...events.map((e) => ({ ...e, at: e.at })),
  ].sort(
    (a, b) =>
      a.at.localeCompare(b.at) ||
      (a.type === "verify" && b.type === "verify"
        ? a.record.id.localeCompare(b.record.id)
        : a.type === "verify"
          ? -1
          : 1),
  );
  const active = new Map();
  return stream.map((e) => {
    if (e.type === "verify") active.set(e.record.id, e.record);
    else active.delete(e.id);
    const best = [...active.values()].sort((a, b) => cmp(a.theta, b.theta))[0];
    return { at: e.at, theta: best?.theta ?? null, type: e.type };
  });
}
