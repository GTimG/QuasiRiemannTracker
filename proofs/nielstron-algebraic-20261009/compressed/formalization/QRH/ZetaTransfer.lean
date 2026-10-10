import QRH.DirichletTargets
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! Actual-object transfer only. The all-Dirichlet premise is not proved here.
The value at one is handled by Mathlib's total-function convention. -/
namespace QRH
open scoped _root_.DirichletCharacter

theorem zeta_of_allDirichlet (h : Targets.AllDirichlet) : Targets.Zeta := by
  intro s hs
  by_cases h_one : s = 1
  · subst s
    exact riemannZeta_one_ne_zero
  · have hpole : ¬ ((1 : DirichletCharacter ℂ 1) = 1 ∧ s = 1) := by
      rintro ⟨_, heq⟩
      exact h_one heq
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      h (1 : DirichletCharacter ℂ 1) hs hpole

end QRH
