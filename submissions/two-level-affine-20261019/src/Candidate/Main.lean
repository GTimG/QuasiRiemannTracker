/- Released under Apache-2.0. Supporting modules retain their upstream notices. -/
import Candidate.Cycle63.Verification

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174963413/200000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  -- The claim `theta`, the class bound rounded up at the ninth digit, in lowest terms.
  have hθ : Cycle63.Arithmetic.theta = 174963413/200000000 := by norm_num [Cycle63.Arithmetic.theta]
  exact Cycle63Verification.allDirichlet χ (hθ.trans_lt hs) hpole

end Candidate
#print axioms Candidate.bound
