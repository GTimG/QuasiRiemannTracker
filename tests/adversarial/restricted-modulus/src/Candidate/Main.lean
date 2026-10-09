import Mathlib
namespace Candidate
open scoped DirichletCharacter
theorem bound (χ : DirichletCharacter ℂ 1) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 := by sorry
end Candidate
