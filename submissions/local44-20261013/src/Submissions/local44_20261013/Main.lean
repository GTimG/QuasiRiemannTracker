/-
Author: nielstron. Licensed under Apache-2.0; see the repository LICENSE.

Local 22/5 moment submission source bundle

This package is distributed under Apache-2.0. Existing source comments,
copyright notices, and attribution are preserved within each original module
body in src/Candidate/Bundles. Module imports are repackaged and local scopes
are enclosed in anonymous sections. Recorded identifier qualifications resolve
name ambiguities exposed by the larger import environments. Recorded spacing
after comparison operators prevents newly imported notation from consuming
identifier prefixes. Declarations keep their original namespaces. The source snapshot and transformation map are
retained with the accompanying packaging evidence, outside this submission.

The following notices are reproduced from their respective source packages.
Their author, tool, and verification statements describe those upstream
packages, not a new endorsement or verification of this submission.

========================================================================
Cycle25 source notice
========================================================================

# Source notices

Copyright 2026 Hailey Collet. New manuscript and formalization material are
licensed under Apache-2.0. See `LICENSE` and `PROVENANCE.md`.

The vendored `formalization/OAI/` source is the exact import closure from
[OpenAI/math](https://github.com/openai/math) at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. It retains its upstream authorship
and Apache-2.0 license. The source inventory records each included module.
The new proof uses that development's original 7/8 nonvanishing theorem as
a weaker initialization, as well as its analytic and arithmetic foundations.

The `Cycle25` development adapts the numerator inversion, conductor allocation,
coefficient estimates and contour assembly of Akash Levy's
[weighted-numerator proof](https://github.com/akashlevy/QuasiRiemannTracker/tree/2fd60c0926b66ea18d7436f5ed55250fd006ab5d/proofs/akashlevy-20261009-weighted-numerator),
revision `2fd60c0926b66ea18d7436f5ed55250fd006ab5d`, and generalizes the moment,
counting and geometric estimates to the quartic endpoint. That source's
license and notice are retained in `licenses/`; its notice describes the
original upstream package. Its previous final nonvanishing theorem is not
used to establish the new endpoint.

The three `ZetaZeroFree/Analytic/Moments/` modules are reused from Hailey
Collet's [4/33 formalization](https://github.com/GTimG/QuasiRiemannTracker/pull/8).
They reorganize and adapt intermediate OpenAI proofs to establish an
unconditional moving-radical moment. The earlier 4/33 nonvanishing theorem
is not a dependency of this submission.

Mathlib, PrimeNumberTheoremAnd, rellich-kondrachov and the remaining Lake
dependencies retain their own authorship and licenses. Their exact revisions
and the required compatibility patches are recorded with the build recipe.
The patches retain the original licenses; only files needed by this proof's
import closure are included.

Lean, Comparator, NanoDa, con-ron, lean4export and the Palomar verification
helpers are used under their respective licenses. Their binaries are not
redistributed. No upstream project or maintainer endorsement is implied.

========================================================================
Akash Levy upstream notice
========================================================================

Akash Levy weighted-numerator quasi-Riemann proof, theta = 10499/12000, 2026-10-09.
Author and human contributor: Akash Levy (GitHub: akashlevy).
GPT-6 Astra (Ultra) was used to discover the proof and perform partial formalization; Opus 5.5 Ultracode was used to complete the formalization and submit the result.

This package is a derivative of the Lean development of OpenAI's "The
Quasi-Riemann Hypothesis" in github.com/openai/math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). The proof imports that
development through the fork github.com/akashlevy/math at
c388e88e6519d139ad2ca5571ef0c7fbf0e245b5 (branch qrh-23-24-pruned), which is
openai/math fd4aeeb2e with unused declarations pruned in place plus separate
23/24 modules that this proof does not import, and through
Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612 (Apache-2.0). The other
pinned dependencies are listed in formalization/lake-manifest.json; the fork's
Lean 4.34.1 compatibility patches for PrimeNumberTheoremAnd
c39a751132c88b6e8080b74c74023fd95b3d8be0 and rellich-kondrachov
70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23 (both Apache-2.0) are applied by
formalization/setup.sh. Apart from the adapted modules and the modified
upstream files noted below, no upstream source is redistributed here; setup.sh
and Lake fetch it at the pinned revisions. The license texts of
openai/math, Mathlib, PrimeNumberTheoremAnd and rellich-kondrachov are
retained in third-party-notices/. UPSTREAM-NOTICE is the tracker's supplied
notice.

New and adapted material: the 228 Lean modules in formalization/WeightedQRH/
(48 of them adaptations of openai/math fd4aeeb2e modules, each marked as
adapted in its header), the Lake workspace files and scripts in
formalization/, the manuscript in manuscript/, the exponent certificate and
the recorded check reports in evidence/. Modified upstream files:
formalization/ComparatorChallenges/WeightedQRHDirichlet.lean and
WeightedQRHHecke.lean are OpenAI's upstream DirichletSevenEighths and
HeckeSevenEighths Comparator challenges (openai/math fd4aeeb2e) with only the
theorem name and the constant changed (WeightedQRHZeta.lean is new), and
evidence/kernels/src/Challenge.lean is the tracker's fixed three-target
template (public/proofs/palomar-20261009/qrh/src/Challenge.lean) with only its
rational literal changed. All of it is licensed under Apache-2.0 (LICENSE);
the adapted and modified files also remain subject to the Apache-2.0 terms
and notices of their sources (third-party-notices/openai-math-LICENSE.txt,
UPSTREAM-NOTICE).

The recorded checks used, without redistributing them, the official Lean
v4.35.0-rc2 release (lake comparator, leanchecker, nanoda_bin, con-ron), Lean
4.34.1, lean4export 076e8e57707e813375e8f9da8bf989799ace9680 and the Lean FRO
Comparator d03acab154d269c06e60e4de7e4cc85deebff94b, under their own licenses.
No upstream author or project, checker project, Palomar, or the tracker's
maintainers is represented as endorsing this result.

========================================================================
Gao local-moment source notice
========================================================================

# Candidate source notice

New local-source argument and exact certificates prepared for Zhongpai Gao,
with AI assistance, 2026. Distributed under Apache-2.0.

The seven-eighths theorem and analytic/arithmetic framework are OpenAI inputs.
The weighted numerator is Akash Levy's input. The variable moment and quartic
source architecture are Hailey Collet's input. Mathematical reuse and exact
source pins are stated in the candidate. Original work retains its authorship;
see UPSTREAM_NOTICE.md. No maintainer or external reviewer endorsement is claimed.
-/

import Submissions.local44_20261013.Bundles.B126

namespace Submissions.local44_20261013
open scoped DirichletCharacter

/-- The canonical all-moduli Dirichlet nonvanishing target. -/
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (87487 / 100000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Submission20261012.Global.dirichlet_nonzero χ s hs hpole
end Submissions.local44_20261013

#print axioms Submissions.local44_20261013.bound
#print Submissions.local44_20261013.bound
