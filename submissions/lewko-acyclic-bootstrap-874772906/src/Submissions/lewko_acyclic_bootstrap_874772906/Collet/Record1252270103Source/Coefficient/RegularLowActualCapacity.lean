/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Supported positive-corner capacities after three actual common allocations.
The OpenAI/Gao raw allocation identities retain every marked frozen width.
A centered difference never supplies simultaneous support of both corners. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighCoordinatesVolume
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.ClippedQuotient
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowActualCapacity
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands QRH.Record1252270103Low
open Admission.SelectedHighCoordinates
local notation "O" => HeckeFamily.O
local instance regularLowCapacityDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type*} [Fintype ι]

theorem input_log_volume (s : Input ι) (w : ι → ℝ) (Z : ℝ)
    (hZ : 1 < Z) (hscale : ∀ i, s.P i = Z ^ w i) :
    Real.logb Z (volume s) = Real.logb Z (s.X₁*s.X₂) + ∑ i, w i := by
  rw [volume, Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _ => s.P_pos i)).ne',
    Real.logb_prod _ _ (fun i _ => (s.P_pos i).ne')]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hscale i, Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem input_plain_log_le_clipped (s : Input ι) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (s.X₁*s.X₂) ≤ length Z s.X₁ + length Z s.X₂ := by
  have h₁ := Real.logb_le_logb_of_le hZ s.X₁_pos (le_max_right 1 s.X₁)
  have h₂ := Real.logb_le_logb_of_le hZ s.X₂_pos (le_max_right 1 s.X₂)
  rw [Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne']
  exact add_le_add h₁ h₂

variable (s : Input ι) (C₁ R : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (τ₁ : Character) (t₁ : ℝ) (C₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ : ℝ) (C₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R B₁ τ₁ t₁)
      C₂ (R*C₁) B₂ τ₂ t₂).pools C₃) (τ₃ : Character) (t₃ : ℝ)

/-- Subtract the actual surviving marked product from the actual full volume.
The total removed width is written as the original sum minus the final live sum;
no marked factor is charged as an ordinary norm. -/
theorem three_plain_log_bound (w : ι → ℝ) (N : ℕ) (b Z t : ℝ)
    (hb : 1 ≤ b) (hZ : 1 < Z) (hN : Fintype.card ι ≤ N) (hu : s.upper ≤ b)
    (hscale : ∀ i, s.P i = Z ^ w i)
    (ht : length Z s.X₁ + length Z s.X₂ ≤ t)
    (hf₁ : frozenCoefficient B₁.val C₁ R s.ν s.W s.P ≠ 0)
    (hf₂ : frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W
      (child s C₁ R B₁ τ₁ t₁).P ≠ 0)
    (hf₃ : frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P ≠ 0) :
    let s₃ := child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
      C₃ ((R*C₁)*C₂) B₃ τ₃ t₃
    Real.logb Z (s₃.X₁*s₃.X₂) ≤
      t - Real.logb Z (C₁.absNorm:ℝ) - Real.logb Z (C₂.absNorm:ℝ) -
      Real.logb Z (C₃.absNorm:ℝ) + ((∑ i, w i) - ∑ i : liveIndices B₃.val, w i.val.val.val) +
      3*(N:ℝ)*Real.logb Z b := by
  intro s₃
  have hl := three_log_volume_bound s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃
    N b Z hb hZ hN hu hf₁ hf₂ hf₃
  have hs₃ : ∀ i : liveIndices B₃.val, s₃.P i = Z ^ w i.val.val.val :=
    fun i => hscale i.val.val.val
  rw [input_log_volume s w Z hZ hscale,
    input_log_volume s₃ (fun i => w i.val.val.val) Z hZ hs₃] at hl
  have hp := (input_plain_log_le_clipped s Z hZ).trans ht
  linarith

end
end QRH.Record1252270103Source.RegularLowActualCapacity
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.input_log_volume
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.input_plain_log_le_clipped
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.three_plain_log_bound
