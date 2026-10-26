/- Fresh canonical entry; supporting sources retain their notices. Apache-2.0. -/
import Candidate.Notices
import Candidate.Record836

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (218709/250000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact record836 χ hs hpole
end Candidate
#print axioms Candidate.bound
