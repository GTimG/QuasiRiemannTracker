import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.State
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The change of base of a natural state: a state at base `Z` is a state at base `Z^c` with its widths and its
puncture cap divided by `c`. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.CenteredMomentEnergyState
open _root_.OAI.SevenEighths.CenteredMomentEnergyState
noncomputable section

namespace NaturalState
open _root_.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState

variable {Z Bmask bΦ : ℝ}

/-- `Z^(c (x/c)) = Z^x` for a base `Z ≥ 1`. -/
theorem rpow_rebase (s : NaturalState Z Bmask bΦ) {c : ℝ} (hc : 0 < c) (x : ℝ) : (Z^c)^(x/c) = Z^x := by
  rw [← Real.rpow_mul (by linarith [s.base_ge_one])]
  congr 1
  field_simp

/-- The state `s` at base `Z` seen at base `Z^c`: the same character, moduli, puncture and radial data, with the row
width, the character width and the puncture cap divided by `c`. -/
def rebase (s : NaturalState Z Bmask bΦ) (c : ℝ) (hc : 0 < c) : NaturalState (Z^c) (Bmask/c) bΦ where
  character := s.character
  fixedModulus := s.fixedModulus
  puncture := s.puncture
  radial := s.radial
  rowWidth := s.rowWidth/c
  characterWidth := s.characterWidth/c
  base_ge_one := Real.one_le_rpow s.base_ge_one hc.le
  row_nonneg := div_nonneg s.row_nonneg hc.le
  character_nonneg := div_nonneg s.character_nonneg hc.le
  scale_eq := by rw [s.scale_eq, _root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.rpow_rebase s hc]
  modulus_bound := by rw [_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.rpow_rebase s hc]; exact s.modulus_bound
  puncture_ne_zero := s.puncture_ne_zero
  puncture_bound := by rw [_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.rpow_rebase s hc]; exact s.puncture_bound
  radial_support := s.radial_support
  row_ne_zero := s.row_ne_zero
  nonexceptional := s.nonexceptional

/-- The width of the state at base `Z^c` is its width at base `Z` divided by `c`. -/
theorem rebase_width (s : NaturalState Z Bmask bΦ) {c : ℝ} (hc : 0 < c) : (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.rebase s c hc).width = s.width/c := by
  unfold width rebase
  ring

/-- The change of base keeps the character. -/
theorem rebase_character (s : NaturalState Z Bmask bΦ) {c : ℝ} (hc : 0 < c) :
    (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.rebase s c hc).character = s.character := rfl

/-- The change of base keeps the fixed modulus. -/
theorem rebase_fixedModulus (s : NaturalState Z Bmask bΦ) {c : ℝ} (hc : 0 < c) :
    (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.rebase s c hc).fixedModulus = s.fixedModulus := rfl

/-- The change of base keeps the mask. -/
theorem rebase_mask (s : NaturalState Z Bmask bΦ) {c : ℝ} (hc : 0 < c) : (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.rebase s c hc).mask = s.mask := rfl

/-- The change of base keeps the radial data, so the energies of the state are the same at both bases. -/
theorem rebase_radial (s : NaturalState Z Bmask bΦ) {c : ℝ} (hc : 0 < c) : (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.rebase s c hc).radial = s.radial := rfl

end NaturalState

end
end OAI.SevenEighths.CenteredMomentEnergyState

end Record1252270103Bootstrap.PR67
