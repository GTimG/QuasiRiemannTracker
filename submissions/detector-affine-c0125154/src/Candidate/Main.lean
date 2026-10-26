/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Bundles.B192

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (437423 / 500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Cycle61Verification.allDirichlet χ hs hpole

end Candidate
#print axioms Candidate.bound
