import { useEffect, useState } from "react";
import type { Rational, Contribution } from "./types";

export type PendingSubmission = {
  id: string;
  head_repository?: string;
  method?: string;
  exact_bound?: string;
  proposal?: boolean;
  entrypoint?: Contribution["entrypoint"];
  license?: string;
  builds_on?: string[];
  references?: Contribution["references"];
  pr: number;
  head_sha: string;
  title: string;
  authors: { name: string }[];
  theta: Rational;
  submitted_at: string;
  state: keyof typeof submissionLabels;
  run_url: string | null;
};
const previewFeed = import.meta.env.VITE_SUBMISSION_STATUS_URL;
export const submissionLabels = {
  "manual-review": "Awaiting maintainer verification",
  draft: "Draft",
  "awaiting-worker": "Awaiting worker setup",
  queued: "Checks queued",
  running: "Checks running",
  "checks-passed": "Checks passed · awaiting review",
  "checks-failed": "Checks did not complete successfully",
  cancelled: "Checks cancelled",
  "dispatch-failed": "Could not queue checks",
  merged: "Merged · awaiting publication",
  closed: "Closed",
  superseded: "Superseded",
};

export function usePendingSubmissions(
  repository: string | null,
  published: { pr: number | null; source_commit: string }[],
) {
  const [records, setRecords] = useState<PendingSubmission[]>([]);
  const [error, setError] = useState("");
  useEffect(() => {
    if (!repository) return;
    const controller = new AbortController();
    const refresh = async () => {
      try {
        const response = await fetch(
          previewFeed ||
            `https://raw.githubusercontent.com/${repository}/submission-status/submissions.json`,
          { signal: controller.signal, cache: "no-store" },
        );
        // The branch is created by the first intake run after this feature is merged.
        if (response.status === 404) return;
        if (!response.ok)
          throw Error(`Submission status unavailable (${response.status}).`);
        const feed = await response.json();
        if (
          feed.schema_version !== 1 ||
          feed.repository !== repository ||
          !Array.isArray(feed.records)
        )
          throw Error("Unsupported submission status data.");
        setRecords(feed.records);
        setError("");
      } catch (error) {
        if (!controller.signal.aborted)
          setError(error instanceof Error ? error.message : String(error));
      }
    };
    void refresh();
    const timer = window.setInterval(refresh, 60_000);
    return () => {
      controller.abort();
      window.clearInterval(timer);
    };
  }, [repository]);
  const pending = records.filter(
    (r) =>
      !["closed", "superseded"].includes(r.state) &&
      !published.some((p) => p.pr === r.pr && p.source_commit === r.head_sha),
  );
  return { pending, error };
}
export function pendingContribution(
  r: PendingSubmission,
  repository: string,
): Contribution {
  return {
    id: `pending-${r.pr}-${r.id}`,
    title: r.title,
    theta: r.theta,
    authors: r.authors,
    method:
      r.method || "Submitted proof; independent checks and review are pending.",
    references: [
      {
        label: "Submission PR",
        url: `https://github.com/${repository}/pull/${r.pr}`,
      },
      {
        label: "Submitted source",
        url: `https://github.com/${r.head_repository || repository}/tree/${r.head_sha}`,
      },
      ...(r.run_url ? [{ label: "Check logs", url: r.run_url }] : []),
      ...(r.references || []).map((ref) => ({
        ...ref,
        url: /^https:\/\//.test(ref.url)
          ? ref.url
          : `https://github.com/${r.head_repository || repository}/blob/${r.head_sha}/${ref.url}`,
      })),
    ],
    license: r.license || "Awaiting review",
    builds_on: r.builds_on || [],
    entrypoint: r.entrypoint || { module: "", declaration: "" },
    submitted_at: r.submitted_at,
    timeline_at: r.submitted_at,
    date_label: "Submitted",
    verification_note: r.proposal
      ? "This is a retuning proposal. The full nonvanishing theorem has not been verified."
      : submissionLabels[r.state],
    published_at: "",
    merged_at: "",
    first_verified_at: "",
    source_commit: r.head_sha,
    repository: r.head_repository || repository,
    pr: r.pr,
    status: "verification-pending",
    exact_bound: r.exact_bound,
    submission_state: r.state,
  };
}
