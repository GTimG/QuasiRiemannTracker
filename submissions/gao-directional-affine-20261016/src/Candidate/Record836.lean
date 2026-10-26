/- Fresh endpoint; predecessor notices are retained. Apache-2.0. -/
import Candidate.Target836.Target836Verification

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter
theorem record836 {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (218709/250000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Target836Verification.allDirichlet χ hs hpole
end Candidate
#print axioms Candidate.record836
