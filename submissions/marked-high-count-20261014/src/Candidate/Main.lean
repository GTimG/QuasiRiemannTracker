/- Released under Apache-2.0. Supporting modules retain their upstream notices. -/
import Candidate.Cycle62.Verification

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (437429/500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Cycle62Verification.allDirichlet χ hs hpole

end Candidate
#print axioms Candidate.bound
