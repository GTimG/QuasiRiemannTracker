import Candidate.Notices
import Candidate.Local.Qrh.PositiveGap.BestEndpoint
set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : ((777 - Real.sqrt 1081) / 852 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact _root_.Qrh.PositiveGap.bound χ hs hpole
end Candidate
#print axioms Candidate.bound
