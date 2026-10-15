/-
Copyright (c) 2026 QuasiRiemannTracker contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Classical theta-one wrappers, prepared with AI assistance.
The proofs apply the Mathlib results credited in NOTICE.
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace Submissions.classical_euler_product

/-- The tracker's all-Dirichlet statement at the classical bound theta = 1. -/
theorem bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1 / 1 : ℝ) < s.re) (_hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  have hs' : (1 : ℝ) < s.re := by simpa only [div_one] using hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs']
  exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs'

/-- The Riemann-zeta specialization at the same exact bound. -/
theorem zeta_bound {s : ℂ} (hs : (1 / 1 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  have hs' : (1 : ℝ) < s.re := by simpa only [div_one] using hs
  exact riemannZeta_ne_zero_of_one_lt_re hs'

end Submissions.classical_euler_product

#print axioms Submissions.classical_euler_product.bound
#print axioms Submissions.classical_euler_product.zeta_bound
