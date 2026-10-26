import Candidate.Cycle63.Physical.FinalCapacity.Allocation
import Candidate.Cycle63.Physical.FinalCapacity.Affine
import Candidate.Cycle63.Physical.FinalCapacity.Geometry

/- Original module: Candidate.Cycle63.Physical.FinalCapacity.Capacity. -/
section

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
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The old 9/2 capacity of an actual surviving residual row is paid by
 its genuine raw volume and the fixed plain-support clipping cost. -/
theorem supported_residual_capacity (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (hP : ∀i,1 ≤ s.P i) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=s.X₁*s.X₂) (z : O)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P L a
      s.W₁ s.W₂ X₁ X₂ ≠ 0) :
    plainLogs L a Z X₁ X₂+(9/2)*remainingLogs L a Z s.P ≤
      Real.logb Z (preVolume s)+(7/2)*(∑i,Real.logb Z (s.P i))+
        Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s L a z X₁ X₂ hX₁ hX₂ hne
  have hc := (clipping_loss_bound Z _ _ s.b₁ s.b₂ hZ
    (rawScale_pos L a X₁ hX₁ 0) (rawScale_pos L a X₂ hX₂ 1) hs₁ hs₂).2
  have hl := remainingLogs_le L a Z hZ s.P hP
  have hr := Real.logb_nonneg hZ (formalReduction_ge_one L a s.P hP)
  have he := affine_exact L a Z X₁ X₂ (3/4) 0 hZ hX₁ hX₂ s.P s.P_pos
  rw [hprod] at he
  change _ = Real.logb Z (preVolume s)-_ - _ + _ + _ at he
  linarith

/-- Two actual common allocations retain the original slot budget; all
 deleted and residual slots are accounted for by their genuine reductions. -/
theorem two_stage_supported_capacity (s : Input ι) (C₁ R₁ : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (χ : Character) (t : ℝ)
    (C₂ R₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z : ℝ) (hZ : 1 < Z) (hP : ∀i,1 ≤ s.P i)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=(commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₁*
      (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₂)
    (z : O) (hne : let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
      allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P L a
        v.W₁ v.W₂ X₁ X₂ ≠ 0) :
    let first := child s C₁ R₁ B₁ χ t
    let final := commonData first C₂ R₂ B₂
    plainLogs L a Z X₁ X₂+(9/2)*remainingLogs L a Z final.P ≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
        Real.logb Z (rawReduction B₂.val first.P)+(7/2)*(∑i,Real.logb Z (s.P i))+
        Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  let first := child s C₁ R₁ B₁ χ t
  let final := commonData first C₂ R₂ B₂
  have hp₁ : ∀i,1 ≤ first.P i := fun i => hP i.val
  have hp₂ : ∀i,1 ≤ final.P i := fun i => hp₁ i.val
  have hb := supported_residual_capacity final L a Z hZ hp₂ X₁ X₂ hX₁ hX₂ hprod z hne
  have hv : Real.logb Z (preVolume final) = Real.logb Z (preVolume s.toData)-
      Real.logb Z (rawReduction B₁.val s.P)-Real.logb Z (rawReduction B₂.val first.P) := by
    rw [common_preVolume,Real.logb_div (preVolume_pos first.toData).ne'
      (rawReduction_pos B₂.val (alloc_ne first C₂ B₂) first.P first.P_pos).ne',
      first_child_prevolume,Real.logb_div (preVolume_pos s.toData).ne'
      (rawReduction_pos B₁.val (alloc_ne s C₁ B₁) s.P s.P_pos).ne']
  have hl₁ := common_slot_logs_le s C₁ B₁ Z hZ hP
  have hl₂ := common_slot_logs_le first C₂ B₂ Z hZ hp₁
  rw [hv] at hb
  change _ ≤ _ at hb ⊢
  change (∑i,Real.logb Z (final.P i)) ≤ ∑i,Real.logb Z (first.P i) at hl₂
  have hl : (∑i,Real.logb Z (final.P i)) ≤ ∑i,Real.logb Z (s.P i) := hl₂.trans hl₁
  change _ ≤ Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
    Real.logb Z (rawReduction B₂.val first.P)+(7/2)*(∑i,Real.logb Z (final.P i))+
      Real.logb Z (max 1 s.b₁*max 1 s.b₂) at hb
  linarith

#print axioms supported_residual_capacity
#print axioms two_stage_supported_capacity
end
end OAI.SevenEighths.Cycle63FinalCapacity
end

/- Original module: Candidate.Cycle63.Physical.FinalCapacity.Final. -/
section

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
    (hz : (17/500)*M ≤ ∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i)) ≤ (1/25)*M)
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
    (hz : (17/500)*M ≤ ∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i)) ≤ (1/25)*M)
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
end
