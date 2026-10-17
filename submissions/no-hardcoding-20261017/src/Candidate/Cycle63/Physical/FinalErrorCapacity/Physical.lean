import Candidate.Cycle63.Physical.FinalErrorCapacity.Capacity
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63FinalErrorCapacity
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
open CenteredMomentCanonicalFirst Cycle63FinalCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Both actual second-label allocations share the same generator/unit
 cancellation. Prime extraction pays its exact removed width. -/
theorem actual_error_source_capacity (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P ≠ 0)
    (χ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q ≠ 0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C₁ R₁ B₁ χ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C₁ R₁ B₁ χ t).pools (Q^k))
    (υ : Character) (v : ℝ) (C₂ D₂ H R₂ : Ideal O) (hH : H=C₂ ∨ H=D₂)
    (B₂ : actualAllocations (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v).pools H)
    (hf₂ : let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
      frozenCoefficient B₂.val H R₂ e.ν e.W e.P ≠ 0)
    (D₁ : Ideal O) (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z M amp omega wo : ℝ) (hZ : 1 < Z) (hM : 0 < M) (hP : ∀i,1 ≤ s.P i)
    (hwo : wo ≤ (k:ℝ)*Real.logb Z (Q.absNorm:ℝ))
    (hz : Cycle63.Optimization.slotFloor*M ≤ ∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i)) ≤ Cycle63.Optimization.slotTop*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle63.Arithmetic.lambda*(∑i,Real.logb Z (s.P i)) ≤ Cycle63.Arithmetic.B*M)
    (second : Bool) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow
      (commonData (twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v) H R₂ B₂).toSource second L a z ≠ 0) :
    let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
    let f := commonData e H R₂ B₂
    let w := (k:ℝ)*Real.logb Z (Q.absNorm:ℝ)
    let cell := Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))
    length Z (Cycle63Moment.LowBranch.finalPlain f second L a 0)+
      length Z (Cycle63Moment.LowBranch.finalPlain f second L a 1)+
        (9/2)*remainingLogs L a Z f.P-
      errorNominal M Z amp omega w wo C₁ D₁ C₂ D₂ U ≤
        M*Cycle63.Arithmetic.g cell+3*amp+(w-wo)+omega+supportPadding N b s.b₁ s.b₂ Z := by
  let first := child s C₁ R₁ B₁ χ t
  let e := twiceChild s C₁ R₁ B₁ χ t Q k Bp υ v
  let f := commonData e H R₂ B₂
  let X := Cycle63.Physical.sourcePlainScales f.toSource second
  have hx₁ := Cycle63Moment.LowBranch.source_plain_positive f second 0
  have hx₂ := Cycle63Moment.LowBranch.source_plain_positive f second 1
  have hprod : X 0*X 1=f.X₁*f.X₂ := by
    cases second
    · rfl
    · exact f.same_product
  have htotal := extracted_supported_capacity s C₁ R₁ B₁ χ t Q hQ k hslot Bp υ v
    H R₂ B₂ L a Z hZ hP (X 0) (X 1) hx₁ hx₂ hprod z hne
  have he : length Z (Cycle63Moment.LowBranch.finalPlain f second L a 0)+
      length Z (Cycle63Moment.LowBranch.finalPlain f second L a 1) =
        plainLogs L a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (rawScale L a (X 0) 0)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (rawScale L a (X 1) 1))) = _
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]
    rfl
  have hc₁ := Real.logb_nonneg hZ (norm_ge_one C₁ (allocation_ne s C₁ B₁))
  have hd₁ := Real.logb_nonneg hZ (norm_ge_one D₁ hD₁)
  have hw : 0 ≤ (k:ℝ)*Real.logb Z (Q.absNorm:ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg hZ (norm_ge_one Q hQ))
  have hmax := extraction_max_loss _ _ _ wo hc₁ hd₁ hw hwo
  have hshift : Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))-
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) ≤ Real.logb Z (H.absNorm:ℝ) := by
    rcases hH with hh|hh
    · rw [hh]
      exact actual_common_shift_le C₂ D₂ hC₂ hD₂ hCD₂ U Z hZ
    · rw [hh]
      exact actual_common_shift_le_right C₂ D₂ hC₂ hD₂ hCD₂ U Z hZ
  have hr₁ := common_reduction_log_lower N b hb s hcard hs C₁ R₁ B₁ hf₁ Z hZ
  have hce : Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val) ≤ N :=
    (live_card_le Bp.val).trans ((live_card_le B₁.val).trans hcard)
  have hr₂ := common_reduction_log_lower N b hb e hce hs H R₂ B₂ hf₂ Z hZ
  have hcell := original_affine_capacity s Z M hZ hM hz haffine
  dsimp only at htotal hcell ⊢
  rw [he]
  change Real.logb Z (preVolume s.toData)+(7/2)*(∑i,Real.logb Z (s.P i)) ≤ _ at hcell
  unfold errorNominal supportPadding
  linarith

#print axioms actual_error_source_capacity

/-- A residual branch with no surviving literal row contributes zero for
 every retained mask and every radial profile. -/
theorem no_surviving_row_energy_zero {α : Type*} [Fintype α] [DecidableEq α]
    (src : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2)))
    (keep : O → Prop) (Φ : SchwartzMap ℝ ℂ) (K : ℝ)
    (hz : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L a z=0) :
    Cycle63Moment.LowBranch.finalPositiveEnergy src second L a keep Φ K=0 := by
  unfold Cycle63Moment.LowBranch.finalPositiveEnergy
  simp only [hz,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,ite_self,tsum_zero]

#print axioms no_surviving_row_energy_zero
end
end OAI.SevenEighths.Cycle63FinalErrorCapacity
