import Mathlib
namespace Candidate
open scoped DirichletCharacter
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) (assumption : DirichletCharacter.LFunction χ s ≠ 0) : DirichletCharacter.LFunction χ s ≠ 0 := assumption
end Candidate
