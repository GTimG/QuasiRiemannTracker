import type { Rational } from "./types";

export const milestones: {
  id: string;
  label: string;
  decimal: string;
  theta: Rational;
  dashed: boolean;
  title: string;
  description: string;
  technical?: string;
  source: { label: string; url: string };
}[] = [
  {
    id: "one",
    label: "1",
    decimal: "1.0",
    theta: { numerator: "1", denominator: "1" },
    dashed: false,
    title: "Classical result",
    description: String.raw`All nontrivial zeros lie in the strip between real parts 0 and 1 (\(0\le\operatorname{Re}s\le1\)).`,
    technical: String.raw`Absolute convergence of the Euler product gives \(L(s,\chi)\ne0\) for \(\operatorname{Re}s>1\). A uniform bound \(\theta<1\), independent of conductor and height, establishes the Dirichlet quasi-Riemann hypothesis. The functional equation then confines nontrivial zeros to \(1-\theta\le\operatorname{Re}s\le\theta\).`,
    source: {
      label: "OpenAI, introduction and continuation principle",
      url: "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L45",
    },
  },
  {
    id: "thirteen-fifteenths",
    label: "13/15",
    decimal: "0.8666…",
    theta: { numerator: "13", denominator: "15" },
    dashed: true,
    title: "Limit of OpenAI’s method",
    description: String.raw`OpenAI’s proof combines several estimates. Tuning their parameters and improving the estimates for counting zeros can lower the bound \(\theta\). In tomoto0’s analysis, this approach reaches a limit at \(13/15=0.8666\ldots\): the bound must stay above that value (\(\theta>13/15\)). Reaching it requires changing the argument.`,
    technical: String.raw`In the cubic-theta exponent model analyzed by tomoto0, the normalization \(M+\ell=1\) and the row count \(R(0)=1\) near the critical line force \(\theta>13/15\), even if the counts are as strong as the density hypothesis predicts. This barrier applies to that model. The analysis assumes that some exponent formulas remain valid beyond the ranges proved in the paper.`,
    source: {
      label: "tomoto0, barrier analysis §2",
      url: "https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/blob/b83a73c6cb626a391e551baafdb7d0cceafaa55a/reports/barrier_analysis.md",
    },
  },
  {
    id: "three-quarters",
    label: "3/4",
    decimal: "0.75",
    theta: { numerator: "3", denominator: "4" },
    dashed: true,
    title: "The three-quarter barrier",
    description: String.raw`Mathematician Acer, who worked on OpenAI’s project, pointed out a further obstruction at \(\theta=3/4\). He expects overcoming this barrier in the method to require a new idea.`,
    source: {
      label: "Acer, 6 October 2026",
      url: "https://x.com/AcerFur/status/2107605089225691372",
    },
  },
  {
    id: "half",
    label: "1/2",
    decimal: "0.5",
    theta: { numerator: "1", denominator: "2" },
    dashed: false,
    title: "Generalized Riemann Hypothesis",
    description: String.raw`At \(\theta=1/2\), the strip becomes a single line containing every nontrivial zero (\(\operatorname{Re}s=1/2\)). Proving this for all Dirichlet \(L\)-functions would establish GRH, including the Riemann hypothesis for the zeta function, and give sharper estimates for the distribution of primes.`,
    technical: String.raw`If \(L(s,\chi)\ne0\) for every Dirichlet character \(\chi\) and every \(\operatorname{Re}s>1/2\), with the principal pole excluded, functional-equation symmetry forces \(\operatorname{Re}\rho=1/2\) for every nontrivial zero \(\rho\). This is GRH for Dirichlet L-functions; the modulus-one case is RH for \(\zeta(s)\).`,
    source: {
      label: "OpenAI, introduction and functional-equation consequence",
      url: "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L98",
    },
  },
];
