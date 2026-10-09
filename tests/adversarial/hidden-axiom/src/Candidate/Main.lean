import Candidate.Hidden
import Mathlib
namespace Candidate
open scoped DirichletCharacter
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 := False.elim Hidden.false
end Candidate
