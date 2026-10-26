/- Canonical endpoint; inherited source notices are retained. Apache-2.0. -/
import Candidate.Notices
import Candidate.Target830.Final

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (87483/100000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact OAI.SevenEighths.Target830.Final.allDirichlet χ hs hpole

end Candidate
#print axioms Candidate.bound
