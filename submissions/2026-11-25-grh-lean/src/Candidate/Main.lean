import Candidate.GRH

/-
Source: https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
directory grh-compact, Apache License 2.0. Its NOTICE reads:

  GRH: a Lean 4 proof of the Generalized Riemann Hypothesis for Dirichlet L-functions
  (compact edition). Copyright 2026 Anthropic, PBC.
  This product is licensed under the Apache License, Version 2.0.
  This product is a rewriting of Levent Alpöge's Lean proof. src/Statements.lean and the names
  and types of the five theorems in src/Main.lean are taken from that proof unchanged;
  lakefile.toml is adapted from it.
  This product depends on, but does not include, Lean 4 and Mathlib, both under the Apache
  License, Version 2.0, and Mathlib's dependencies.
  src/Lib/General/LinearAlgebra/Base.lean restates about twenty lemma statements on matrices
  from Mathlib (copyright the Mathlib authors, Apache License, Version 2.0) for classical
  decidability.
  Some declarations, or parts of their proofs, adapt definitions, statements and proofs from
  Mathlib, with changes (copyright the Mathlib authors, Apache License, Version 2.0).
  See ATTRIBUTION.md (in grh-compact at that commit; its src/ is Candidate/ here).

Changes for QuasiRiemannTracker: modules re-rooted under Candidate (upstream Main is
Candidate.GRH), lakefile leanOptions set in each file, this wrapper added, and 42 files
adapted from Lean v4.35.0 / Mathlib 56a00585 to Lean v4.34.1 / Mathlib d13f23b.
-/

/-! QRH entry point: Dirichlet nonvanishing for `1/2 < re s`, from the grh-lean proof
(`LFunction_ne_zero_of_half_lt_re` in `Candidate/GRH.lean`). -/

namespace Candidate

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_half_lt_re q χ s hs (by tauto)

end Candidate
