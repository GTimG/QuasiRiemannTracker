import Candidate.Cycle63.Physical.FinalCapacity.Capacity
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63FinalCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CompletedGauss CanonicalQuadraticSieve CenteredMomentEnergyBands
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nominal width from the genuine second transform. Its common
 frequency/unit shift is kept literal. -/
def secondNominal (M Z amp omega : ℝ) (C₁ D₁ C₂ D₂ : Ideal O)
    (U : Finset (CommonIndex C₂ D₂)) : ℝ :=
  M-max (Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (D₁.absNorm:ℝ)) 0-6*amp-omega-
    Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)

/-- This support error is fixed before the original live input, both
 common allocations, the residual selection, and every frequency/height. -/
def supportPadding (N : ℕ) (b b₁ b₂ Z : ℝ) : ℝ :=
  2*(N:ℝ)*Real.logb Z b+Real.logb Z (max 1 b₁*max 1 b₂)

/-- The substantive final total-capacity gate. Original affine lengths pay
 the raw volume; actual common coefficients pay both divisor shifts; a
 nonzero final row pays its own selected-plain clipping. -/
theorem actual_final_capacity (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P ≠ 0)
    (χ : Character) (t : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (hf₂ : let first := child s C₁ R₁ B₁ χ t
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P ≠ 0)
    (D₁ D₂ : Ideal O) (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z M amp omega : ℝ) (hZ : 1 < Z) (hM : 0 < M) (hP : ∀i,1 ≤ s.P i)
    (hz : Cycle63.Optimization.slotFloor*M ≤ ∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i)) ≤ Cycle63.Optimization.slotTop*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle63.Arithmetic.lambda*(∑i,Real.logb Z (s.P i)) ≤ Cycle63.Arithmetic.B*M)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=(commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₁*
      (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₂)
    (z : O) (hne : let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
      allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P L a
        v.W₁ v.W₂ X₁ X₂ ≠ 0) :
    let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
    let cell := Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))
    plainLogs L a Z X₁ X₂+(9/2)*remainingLogs L a Z v.P-
      secondNominal M Z amp omega C₁ D₁ C₂ D₂ U ≤
        M*Cycle63.Arithmetic.g cell+6*amp+omega+supportPadding N b s.b₁ s.b₂ Z := by
  have hc₁ := Real.logb_nonneg hZ (norm_ge_one C₁ (allocation_ne s C₁ B₁))
  have hd₁ := Real.logb_nonneg hZ (norm_ge_one D₁ hD₁)
  have hmax : max (Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (D₁.absNorm:ℝ)) 0 ≤
      Real.logb Z (C₁.absNorm:ℝ) := max_le (by linarith) hc₁
  have hshift := actual_common_shift_le C₂ D₂ hC₂ hD₂ hCD₂ U Z hZ
  have hr₁ := common_reduction_log_lower N b hb s hcard hs C₁ R₁ B₁ hf₁ Z hZ
  have hr₂ := common_reduction_log_lower N b hb (child s C₁ R₁ B₁ χ t)
    ((live_card_le B₁.val).trans hcard) hs C₂ R₂ B₂ hf₂ Z hZ
  have hcell := original_affine_capacity s Z M hZ hM hz haffine
  have htotal := two_stage_supported_capacity s C₁ R₁ B₁ χ t C₂ R₂ B₂ L a
    Z hZ hP X₁ X₂ hX₁ hX₂ hprod z hne
  dsimp only at hcell htotal ⊢
  change Real.logb Z (preVolume s.toData)+(7/2)*(∑i,Real.logb Z (s.P i)) ≤ _ at hcell
  unfold secondNominal supportPadding
  linarith

/-- Right allocation of the same actual second-transform label pair. -/
theorem actual_final_capacity_right (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P ≠ 0)
    (χ : Character) (t : ℝ) (C₂ D₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools D₂)
    (hf₂ : let first := child s C₁ R₁ B₁ χ t
      frozenCoefficient B₂.val D₂ R₂ first.ν first.W first.P ≠ 0)
    (D₁ : Ideal O) (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z M amp omega : ℝ) (hZ : 1 < Z) (hM : 0 < M) (hP : ∀i,1 ≤ s.P i)
    (hz : Cycle63.Optimization.slotFloor*M ≤ ∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i)) ≤ Cycle63.Optimization.slotTop*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle63.Arithmetic.lambda*(∑i,Real.logb Z (s.P i)) ≤ Cycle63.Arithmetic.B*M)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=(commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂).X₁*
      (commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂).X₂)
    (z : O) (hne : let v := commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂
      allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P L a
        v.W₁ v.W₂ X₁ X₂ ≠ 0) :
    let v := commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂
    let cell := Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))
    plainLogs L a Z X₁ X₂+(9/2)*remainingLogs L a Z v.P-
      secondNominal M Z amp omega C₁ D₁ C₂ D₂ U ≤
        M*Cycle63.Arithmetic.g cell+6*amp+omega+supportPadding N b s.b₁ s.b₂ Z := by
  have hc₁ := Real.logb_nonneg hZ (norm_ge_one C₁ (allocation_ne s C₁ B₁))
  have hd₁ := Real.logb_nonneg hZ (norm_ge_one D₁ hD₁)
  have hmax : max (Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (D₁.absNorm:ℝ)) 0 ≤
      Real.logb Z (C₁.absNorm:ℝ) := max_le (by linarith) hc₁
  have hshift := actual_common_shift_le_right C₂ D₂ hC₂ hD₂ hCD₂ U Z hZ
  have hr₁ := common_reduction_log_lower N b hb s hcard hs C₁ R₁ B₁ hf₁ Z hZ
  have hr₂ := common_reduction_log_lower N b hb (child s C₁ R₁ B₁ χ t)
    ((live_card_le B₁.val).trans hcard) hs D₂ R₂ B₂ hf₂ Z hZ
  have hcell := original_affine_capacity s Z M hZ hM hz haffine
  have htotal := two_stage_supported_capacity s C₁ R₁ B₁ χ t D₂ R₂ B₂ L a
    Z hZ hP X₁ X₂ hX₁ hX₂ hprod z hne
  dsimp only at hcell htotal ⊢
  change Real.logb Z (preVolume s.toData)+(7/2)*(∑i,Real.logb Z (s.P i)) ≤ _ at hcell
  unfold secondNominal supportPadding
  linarith


#print axioms secondNominal
#print axioms supportPadding
#print axioms actual_final_capacity
#print axioms actual_final_capacity_right
end
end OAI.SevenEighths.Cycle63FinalCapacity
