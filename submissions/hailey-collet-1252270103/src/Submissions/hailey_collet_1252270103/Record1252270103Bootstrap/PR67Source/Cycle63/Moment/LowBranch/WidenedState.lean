import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.FixedDeletion
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- A natural state may be given a larger bound for the width of its character without changing its energy.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands

/-- The state with the width bound of its character raised so that its total width is `W`, for `W` at least the
width of the state. The width of a natural state only bounds the norm of the modulus of its character from above, so
the raised state has the same character, mask, rows and radial profile. -/
def widenState {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (W : ℝ) (hW : s.width ≤ W) :
    NaturalState Z Bmask bΦ :=
  { s with
    characterWidth := s.characterWidth + (W - s.width)
    character_nonneg := add_nonneg s.character_nonneg (sub_nonneg.mpr hW)
    modulus_bound := s.modulus_bound.trans
      (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith [sub_nonneg.mpr hW])) }

/-- The widened state has the total width `W`. -/
theorem widenState_width {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (W : ℝ) (hW : s.width ≤ W) :
    (widenState s W hW).width = W := by
  unfold NaturalState.width widenState
  unfold NaturalState.width at hW ⊢
  simp only
  ring

/-- The widened state has the same character. -/
theorem widenState_character {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (W : ℝ) (hW : s.width ≤ W) :
    (widenState s W hW).character = s.character := rfl

/-- The widened state has the same fixed modulus. -/
theorem widenState_fixedModulus {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (W : ℝ) (hW : s.width ≤ W) :
    (widenState s W hW).fixedModulus = s.fixedModulus := rfl

/-- The widened state has the same mask. -/
theorem widenState_mask {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (W : ℝ) (hW : s.width ≤ W) :
    (widenState s W hW).mask = s.mask := rfl

/-- The widened state has the same radial data. -/
theorem widenState_radial {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (W : ℝ) (hW : s.width ≤ W) :
    (widenState s W hW).radial = s.radial := rfl

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
