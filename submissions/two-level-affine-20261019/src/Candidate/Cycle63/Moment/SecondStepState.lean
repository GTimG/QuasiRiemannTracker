/- A natural state of the second step in the unit of its width: seen at the base `Z^width`, where its width is one,
with the bound of the norm of its puncture restated. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.StateRebase
import Candidate.Cycle63.Moment.DepthTwoPresented

set_option autoImplicit false

namespace OAI.SevenEighths.CenteredMomentEnergyState
noncomputable section

namespace NaturalState

variable {Z Bmask bΦ : ℝ}

/-- The state with the bound of the norm of its puncture restated as `Z^Bmask'`, for an exponent `Bmask'` that bounds
it. -/
def withMask (s : NaturalState Z Bmask bΦ) (Bmask' : ℝ) (h : (s.puncture.absNorm : ℝ) ≤ Z ^ Bmask') :
    NaturalState Z Bmask' bΦ where
  character := s.character
  fixedModulus := s.fixedModulus
  puncture := s.puncture
  radial := s.radial
  rowWidth := s.rowWidth
  characterWidth := s.characterWidth
  base_ge_one := s.base_ge_one
  row_nonneg := s.row_nonneg
  character_nonneg := s.character_nonneg
  scale_eq := s.scale_eq
  modulus_bound := s.modulus_bound
  puncture_ne_zero := s.puncture_ne_zero
  puncture_bound := h
  radial_support := s.radial_support
  row_ne_zero := s.row_ne_zero
  nonexceptional := s.nonexceptional

/-- The state in the unit of its width: at the base `Z^width`, where its width is one, with the mask bound `Bwide`
for the norm of its puncture. -/
def unitState (s : NaturalState Z Bmask bΦ) (hW : 0 < s.width) (Bwide : ℝ)
    (h : (s.puncture.absNorm : ℝ) ≤ (Z ^ s.width) ^ Bwide) : NaturalState (Z ^ s.width) Bwide bΦ :=
  (s.rebase s.width hW).withMask Bwide h

variable (s : NaturalState Z Bmask bΦ) (hW : 0 < s.width) (Bwide : ℝ)
  (h : (s.puncture.absNorm : ℝ) ≤ (Z ^ s.width) ^ Bwide)

/-- The state in the unit of its width has width one. -/
theorem unitState_width : (s.unitState hW Bwide h).width = 1 := by
  change (s.rebase s.width hW).width = 1
  rw [rebase_width]
  exact div_self hW.ne'

/-- The row width of the state in the unit of its width is the row width divided by the width. -/
theorem unitState_rowWidth : (s.unitState hW Bwide h).rowWidth = s.rowWidth / s.width := rfl

/-- The row width of the state in the unit of its width is at most one. -/
theorem unitState_rowWidth_le_one : (s.unitState hW Bwide h).rowWidth ≤ 1 := by
  have h1 := s.unitState_width hW Bwide h
  have h2 := (s.unitState hW Bwide h).character_nonneg
  unfold width at h1
  linarith

end NaturalState

end
end OAI.SevenEighths.CenteredMomentEnergyState

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open Filter HeckeFamily CenteredMomentEnergyState
local notation "O" => HeckeFamily.O

/-- A presented state, seen in the unit of its width, is presented at the height exponent divided by the width. -/
theorem DepthTwoPresented.unitState {τT Bmask bΦ Z T : ℝ} {η₀ : Character} {s : NaturalState Z Bmask bΦ} {v₁ : O}
    (hs : DepthTwoPresented τT η₀ Z s v₁ T) (hW : 0 < s.width) (Bwide : ℝ)
    (h : (s.puncture.absNorm : ℝ) ≤ (Z ^ s.width) ^ Bwide) :
    DepthTwoPresented (τT / s.width) η₀ (Z ^ s.width) (s.unitState hW Bwide h) v₁ T := by
  obtain ⟨⟨h₁, h₂⟩, hrest⟩ := hs
  refine ⟨⟨?_, ?_⟩, hrest⟩
  · rw [s.rpow_rebase hW]
    exact h₁
  · rw [s.rpow_rebase hW]
    exact h₂

/-- The logarithm to the base `Z^c` is the logarithm to the base `Z` divided by `c`. -/
theorem length_rpow {Z c : ℝ} (hZ : 0 < Z) (X : ℝ) :
    CenteredMomentEnergyBands.length (Z ^ c) X = CenteredMomentEnergyBands.length Z X / c := by
  unfold CenteredMomentEnergyBands.length
  rw [Real.logb, Real.logb, Real.log_rpow hZ, div_div, mul_comm]

/-- Seen at the base `Z^c` the exponent `x / c` gives the same number as the exponent `x` at the base `Z`. -/
theorem rpow_rpow_div {Z c : ℝ} (hZ : 0 ≤ Z) (hc : c ≠ 0) (x : ℝ) : (Z ^ c) ^ (x / c) = Z ^ x := by
  rw [← Real.rpow_mul hZ]
  congr 1
  field_simp

/-- A bound `Z^a` of a quantity is a bound `(Z^W)^b` at the base `Z^W`, when `a ≤ W*b`. -/
theorem le_rpow_rpow_of_le_mul {Z W a b N : ℝ} (hZ : 1 ≤ Z) (h : N ≤ Z ^ a) (hab : a ≤ W * b) :
    N ≤ (Z ^ W) ^ b :=
  h.trans ((Real.rpow_le_rpow_of_exponent_le hZ hab).trans_eq (Real.rpow_mul (zero_le_one.trans hZ) W b))

/-- An eventual property of the base holds for the bases `Z^c` with `c` at least a positive `c₀`, for all large `Z`. -/
theorem eventually_rpow_ge {P : ℝ → Prop} (h : ∀ᶠ Z' in atTop, P Z') {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∀ᶠ Z in atTop, 1 < Z ∧ ∀ c : ℝ, c₀ ≤ c → P (Z ^ c) := by
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp h
  have hten : Tendsto (fun Z : ℝ => Z ^ c₀) atTop atTop := tendsto_rpow_atTop hc₀
  filter_upwards [eventually_gt_atTop (1 : ℝ), hten.eventually (eventually_ge_atTop Z₀)] with Z hZ hZc
  exact ⟨hZ, fun c hc => hZ₀ _ (hZc.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hc))⟩

end
end OAI.SevenEighths.Cycle63Moment
