/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Each literal positive corner supplies its own support or vanishes exactly. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowActualCapacity
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowActualCapacity
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentSourceMass QRH.Record1252270103Low
open QRH.Record1252270103Restoration
local notation "O" => HeckeFamily.O
local instance regularLowCornersDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- This uses membership in the original finite ordinary pool. Neither a
character zero nor a profile zero is removed from the positive row. -/
theorem plain_sum_scale_support (ψ : Ideal O →*₀ ℂ) (W₁ W₂ : ℝ → ℂ)
    (b X₁ X₂ : ℝ) (hne : squarefreePlainSum ψ W₁ W₂ b X₁ X₂ ≠ 0) :
    1 ≤ b*X₁ ∧ 1 ≤ b*X₂ := by
  obtain ⟨n,hn,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hn
  have hi' := (mem_idealBall _ _).mp hi
  have hj' := (mem_idealBall _ _).mp hj
  have norm_one (I : Ideal O) (hI : I ≠ 0) : (1:ℝ) ≤ I.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact ⟨(norm_one n.1 hi'.1).trans hi'.2,(norm_one n.2 hj'.1).trans hj'.2⟩

theorem positive_slot_scale_support (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (b : ℝ) (S : κ → Finset (Ideal O))
    (β : κ → Ideal O → ℂ) (P : κ → ℝ) (height X₁ X₂ : ℝ)
    (hne : squarefreePositiveSlotRow η m A z W₁ W₂ b S β P height X₁ X₂ ≠ 0) :
    1 ≤ b*X₁ ∧ 1 ≤ b*X₂ := by
  exact plain_sum_scale_support _ W₁ W₂ b X₁ X₂
    (left_ne_zero_of_mul (right_ne_zero_of_mul hne))

theorem supported_quotient_clipping (Z X₁ X₂ d₁ d₂ b : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (h₁ : 1 ≤ b*(X₁/d₁)) (h₂ : 1 ≤ b*(X₂/d₂)) :
    length Z (X₁/d₁) + length Z (X₂/d₂) ≤
      Real.logb Z (X₁*X₂) - Real.logb Z d₁ - Real.logb Z d₂ +
        2*Real.logb Z (max 1 b) := by
  have hx := (clipped_log_of_scale_support Z (X₁/d₁) b hZ (div_pos hX₁ hd₁) h₁).2
  have hy := (clipped_log_of_scale_support Z (X₂/d₂) b hZ (div_pos hX₂ hd₂) h₂).2
  rw [Real.logb_div hX₁.ne' hd₁.ne'] at hx
  rw [Real.logb_div hX₂.ne' hd₂.ne'] at hy
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  linarith

variable (s : Input ι) (C₁ R : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (τ₁ : Character) (t₁ : ℝ) (C₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ : ℝ) (C₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R B₁ τ₁ t₁)
      C₂ (R*C₁) B₂ τ₂ t₂).pools C₃) (τ₃ : Character) (t₃ : ℝ)

/-- Apply separately with the actual X corner and the actual Y corner.
The product identity is preserved by the three allocations; the support
alternative is extracted from this very positive row, not the centered row. -/
theorem three_positive_corner_capacity_or_zero (w : ι → ℝ) (N : ℕ)
    (upper Z t : ℝ) (hb : 1 ≤ upper) (hZ : 1 < Z)
    (hN : Fintype.card ι ≤ N) (hu : s.upper ≤ upper)
    (hscale : ∀ i, s.P i = Z ^ w i)
    (ht : length Z s.X₁ + length Z s.X₂ ≤ t)
    (hf₁ : frozenCoefficient B₁.val C₁ R s.ν s.W s.P ≠ 0)
    (hf₂ : frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W
      (child s C₁ R B₁ τ₁ t₁).P ≠ 0)
    (hf₃ : frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P ≠ 0)
    (X₁ X₂ d₁ d₂ b : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hprod : X₁*X₂ =
      (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
        C₃ ((R*C₁)*C₂) B₃ τ₃ t₃).X₁ *
      (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
        C₃ ((R*C₁)*C₂) B₃ τ₃ t₃).X₂)
    (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : κ → Finset (Ideal O)) (β : κ → Ideal O → ℂ) (P : κ → ℝ) (height : ℝ) :
    squarefreePositiveSlotRow η m A z W₁ W₂ b S β P height (X₁/d₁) (X₂/d₂) = 0 ∨
    length Z (X₁/d₁) + length Z (X₂/d₂) ≤
      t - Real.logb Z (C₁.absNorm:ℝ) - Real.logb Z (C₂.absNorm:ℝ) -
      Real.logb Z (C₃.absNorm:ℝ) + ((∑ i, w i) - ∑ i : liveIndices B₃.val, w i.val.val.val) +
      3*(N:ℝ)*Real.logb Z upper - Real.logb Z d₁ - Real.logb Z d₂ +
      2*Real.logb Z (max 1 b) := by
  by_cases hz : squarefreePositiveSlotRow η m A z W₁ W₂ b S β P height (X₁/d₁) (X₂/d₂) = 0
  · exact Or.inl hz
  · apply Or.inr
    have hs := positive_slot_scale_support η m A z W₁ W₂ b S β P height _ _ hz
    have hc := supported_quotient_clipping Z X₁ X₂ d₁ d₂ b hZ hX₁ hX₂ hd₁ hd₂ hs.1 hs.2
    have hp := three_plain_log_bound s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃
      w N upper Z t hb hZ hN hu hscale ht hf₁ hf₂ hf₃
    rw [hprod] at hc
    exact hc.trans (by linarith only [hp])

end
end QRH.Record1252270103Source.RegularLowActualCapacity
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.plain_sum_scale_support
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.positive_slot_scale_support
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.supported_quotient_clipping
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.three_positive_corner_capacity_or_zero
