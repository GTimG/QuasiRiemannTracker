/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Assembly.Unconditional
import Candidate.Cycle63.Optimization.SplitOptimality

set_option autoImplicit false
namespace Cycle63Verification
open scoped _root_.DirichletCharacter
open Cycle63.FinalAssembly

theorem allDirichlet {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : Cycle63.Arithmetic.theta < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact dirichlet_nonzero_of_chosen_affine detector_affine_input chosen_affine_input χ s hs hpole

theorem zeta {s : ℂ}
    (hs : Cycle63.Arithmetic.theta < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  exact zeta_nonzero_off_pole_of_chosen_affine detector_affine_input chosen_affine_input s hs hpole

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : Cycle63.Arithmetic.theta < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact hecke_nonzero_of_chosen_affine detector_affine_input chosen_affine_input χ s hs (by tauto)

/-- Mathlib's total zeta function also has a nonzero value at its pole. -/
theorem zetaTotal {s : ℂ} (hs : Cycle63.Arithmetic.theta < s.re) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_nonzero_of_chosen_affine detector_affine_input chosen_affine_input s hs

end Cycle63Verification
#print axioms Cycle63Verification.allDirichlet
#print axioms Cycle63Verification.zeta
#print axioms Cycle63Verification.allHecke
#print axioms Cycle63Verification.zetaTotal
#print axioms Cycle63.Optimization.markedSplit_optimal
