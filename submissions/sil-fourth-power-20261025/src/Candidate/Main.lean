/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.FourthPower.RepairedUnconditionalEndpoint

set_option autoImplicit false

namespace Candidate
open scoped _root_.DirichletCharacter

/-- Dirichlet nonvanishing in the strict half-plane Re(s) > 1749387/2000000. -/
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1749387 / 2000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact FourthPower.RepairedUnconditionalEndpoint.dirichlet_nonvanishing χ hs hpole

end Candidate
