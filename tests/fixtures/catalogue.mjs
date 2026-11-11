// Deliberately synthetic records: these describe UI/validation scenarios, not
// the repository's admitted results. Each call gives tests independent data.
export function record(overrides = {}) {
  const value = {
    id: "fixture-baseline",
    title: "Example author · Initial bound",
    authors: [{ name: "Example author" }],
    theta: { numerator: "7", denominator: "8" },
    status: "framework-verified",
    timeline_at: "2030-10-02T00:00:00Z",
    date_label: "Published",
    first_verified_at: "2030-10-03T12:00:00Z",
    submitted_at: "2030-10-02T08:00:00Z",
    merged_at: "2030-10-03T13:00:00Z",
    published_at: "2030-10-02T00:00:00Z",
    entrypoint: { module: "Candidate.Main", declaration: "Candidate.bound" },
    method: "Synthetic proof description for catalogue behavior tests.",
    verification_note: "Checked by the example verifier.",
    license: "Apache-2.0",
    builds_on: [],
    references: [{ label: "Publication", url: "https://example.com/paper" }],
    repository: "example/proofs",
    source_commit: "a".repeat(40),
    pr: null,
    solution_url: `https://github.com/example/proofs/blob/${"a".repeat(40)}/Candidate/Main.lean`,
    certificate_url: "certificates/fixture-baseline.json",
    ...overrides,
  };
  if (!overrides.references) {
    if (value.certificate_url)
      value.references.push({
        label: "Verification record",
        url: value.certificate_url,
      });
    if (value.solution_url)
      value.references.push({
        label: "Checked Lean solution",
        url: value.solution_url,
      });
  }
  return value;
}

export function algebraicRecord(overrides = {}) {
  return record({
    id: "fixture-algebraic",
    title: "Example algebraic threshold",
    status: "verification-pending",
    theta: {
      numerator: "87495706979916874001834000695887923",
      denominator: "100000000000000000000000000000000000",
    },
    exact_bound: "(1507 − 2√921) / 1653",
    timeline_at: "2030-10-06T00:00:00Z",
    date_label: "Submitted",
    first_verified_at: "",
    certificate_url: undefined,
    solution_url: undefined,
    ...overrides,
  });
}

export function historicalRecord(overrides = {}) {
  return record({
    id: "fixture-historical",
    title: "Example historical boundary",
    status: "historical-baseline",
    theta: { numerator: "1", denominator: "1" },
    timeline_at: "1922-01-01T00:00:00Z",
    date_precision: "year",
    date_label: "Publication year",
    first_verified_at: "",
    receipt_url: "",
    log_url: "",
    solution_url: undefined,
    certificate_url: undefined,
    ...overrides,
  });
}

export function catalogue() {
  return {
    schema_version: 1,
    records: [
      record(),
      record({
        id: "fixture-improvement",
        title: "Example researcher · Improved bound",
        authors: [{ name: "Example researcher" }],
        theta: { numerator: "8749", denominator: "10000" },
        timeline_at: "2030-10-08T00:00:00Z",
        first_verified_at: "2030-10-10T12:00:00Z",
        builds_on: ["fixture-baseline"],
        certificate_url: "certificates/fixture-improvement.json",
      }),
      record({
        id: "fixture-newest",
        title: "Example team · Newest improvement",
        authors: [{ name: "Example team" }],
        theta: { numerator: "87489", denominator: "100000" },
        timeline_at: "2030-10-09T00:00:00Z",
        first_verified_at: "2030-10-11T12:00:00Z",
        builds_on: ["fixture-improvement"],
        certificate_url: "certificates/fixture-newest.json",
      }),
      algebraicRecord(),
      historicalRecord(),
    ],
  };
}
