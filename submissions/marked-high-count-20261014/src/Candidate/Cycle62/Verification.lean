/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Assembly.Unconditional

set_option autoImplicit false
namespace Cycle62Verification
open scoped _root_.DirichletCharacter
open Cycle62.FinalAssembly

theorem allDirichlet {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (437429/500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact dirichlet_nonzero_of_chosen_affine chosen_affine_input χ s hs hpole

theorem zeta {s : ℂ}
    (hs : (437429/500000 : ℝ) < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  exact zeta_nonzero_off_pole_of_chosen_affine chosen_affine_input s hs hpole

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (437429/500000 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact hecke_nonzero_of_chosen_affine chosen_affine_input χ s hs (by tauto)

/-- Mathlib's total zeta function also has a nonzero value at its pole. -/
theorem zetaTotal {s : ℂ} (hs : (437429/500000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_nonzero_of_chosen_affine chosen_affine_input s hs

end Cycle62Verification
#print axioms Cycle62Verification.allDirichlet
#print axioms Cycle62Verification.zeta
#print axioms Cycle62Verification.allHecke
#print axioms Cycle62Verification.zetaTotal
