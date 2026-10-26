/- Fresh endpoint verification; predecessor attribution retained. Apache-2.0. -/
import Candidate.Target836.Target836Unconditional

set_option autoImplicit false
namespace Target836Verification
open scoped _root_.DirichletCharacter
open Target836.FinalAssembly

theorem allDirichlet {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (218709/250000:ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact dirichlet_nonzero_of_chosen_affine
    OAI.SevenEighths.Target836InitialSupplier.actual_detector_affine_input
    chosen_affine_input χ s hs hpole

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (218709/250000:ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact hecke_nonzero_of_chosen_affine
    OAI.SevenEighths.Target836InitialSupplier.actual_detector_affine_input
    chosen_affine_input χ s hs (by tauto)

theorem zeta {s : ℂ} (hs : (218709/250000:ℝ) < s.re) (_hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  exact zeta_nonzero_off_pole_of_chosen_affine
    OAI.SevenEighths.Target836InitialSupplier.actual_detector_affine_input
    chosen_affine_input s hs _hpole

end Target836Verification
#print axioms Target836Verification.allDirichlet
#print axioms Target836Verification.allHecke
#print axioms Target836Verification.zeta
