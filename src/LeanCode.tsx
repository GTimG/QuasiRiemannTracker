import { useMemo } from "react";
import { ExternalLink } from "lucide-react";
import { createHighlighterCoreSync } from "shiki/core";
import { createJavaScriptRegexEngine } from "shiki/engine/javascript";
import lean from "@shikijs/langs/lean";
import githubLight from "@shikijs/themes/github-light";

const highlighter = createHighlighterCoreSync({
  langs: [lean],
  themes: [githubLight],
  engine: createJavaScriptRegexEngine(),
});

export default function LeanCode({
  code,
  source,
}: {
  code: string;
  source: string;
}) {
  const html = useMemo(
    () => highlighter.codeToHtml(code, { lang: "lean", theme: "github-light" }),
    [code],
  );
  return (
    <div className="lean-code">
      <div className="lean-code-heading">
        <span>Lean</span>
        <a href={source} target="_blank" rel="noreferrer">
          Upstream theorem specification{" "}
          <ExternalLink size={13} aria-hidden="true" />
        </a>
      </div>
      <div dangerouslySetInnerHTML={{ __html: html }} />
    </div>
  );
}
