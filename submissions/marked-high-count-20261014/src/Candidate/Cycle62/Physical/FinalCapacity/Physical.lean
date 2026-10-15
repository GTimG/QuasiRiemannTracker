import Candidate.Cycle62.Physical.FinalCapacity.Final
import Candidate.Cycle62.Moment.LowBranch.SideGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle62FinalCapacity
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

open CenteredMomentRetainedProfile

omit [DecidableEq ι] in
/-- Independent second characters and Mellin heights change no allocation
 or capacity scale. This identifies the actual second source dictionary. -/
theorem child_with_height (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (χ ψ : Character) (t v : ℝ) :
    CenteredMomentCommonHeightEnvelope.withHeight (child s C R B χ t) ψ v =
      child s C R B ψ v := by
  rfl

/-- Literal final selected-plain lengths and the literal physical positive row.
 Both signed rectangles inherit the capacity theorem without a scale hypothesis. -/
theorem actual_final_source_capacity (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
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
      Cycle62.Arithmetic.lambda*(∑i,Real.logb Z (s.P i)) ≤ Cycle62.Arithmetic.B*M)
    (second : Bool) (z : O)
    (hne : Cycle62.Physical.sourcePositiveRow
      (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).toSource second L a z ≠ 0) :
    let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
    let cell := Cycle62.Arithmetic.cellUpper
      (Cycle62.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))
    length Z (Cycle62Moment.LowBranch.finalPlain v second L a 0)+
      length Z (Cycle62Moment.LowBranch.finalPlain v second L a 1)+
        (9/2)*remainingLogs L a Z v.P-
      secondNominal M Z amp omega C₁ D₁ C₂ D₂ U ≤
        M*Cycle62.Arithmetic.g cell+6*amp+omega+supportPadding N b s.b₁ s.b₂ Z := by
  let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
  let X := Cycle62.Physical.sourcePlainScales v.toSource second
  have hx₁ := Cycle62Moment.LowBranch.source_plain_positive v second 0
  have hx₂ := Cycle62Moment.LowBranch.source_plain_positive v second 1
  have hprod : X 0*X 1=v.X₁*v.X₂ := by
    cases second
    · rfl
    · exact v.same_product
  have hb := actual_final_capacity N b hb s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂
    D₁ D₂ hD₁ hC₂ hD₂ hCD₂ U L a Z M amp omega hZ hM hP hz haffine
    (X 0) (X 1) hx₁ hx₂ hprod z hne
  have he : length Z (Cycle62Moment.LowBranch.finalPlain v second L a 0)+
      length Z (Cycle62Moment.LowBranch.finalPlain v second L a 1) =
        plainLogs L a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (clippedScale (rawScale L a (X 0) 0)))+
      Real.logb Z (max 1 (clippedScale (rawScale L a (X 1) 1))) = _
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]
    rfl
  dsimp only at hb ⊢
  rw [he]
  exact hb

/-- Literal right-source daughter for the unchanged partition U. -/
theorem actual_final_source_capacity_right (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
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
      Cycle62.Arithmetic.lambda*(∑i,Real.logb Z (s.P i)) ≤ Cycle62.Arithmetic.B*M)
    (second : Bool) (z : O)
    (hne : Cycle62.Physical.sourcePositiveRow
      (commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂).toSource second L a z ≠ 0) :
    let v := commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂
    let cell := Cycle62.Arithmetic.cellUpper
      (Cycle62.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))
    length Z (Cycle62Moment.LowBranch.finalPlain v second L a 0)+
      length Z (Cycle62Moment.LowBranch.finalPlain v second L a 1)+
        (9/2)*remainingLogs L a Z v.P-
      secondNominal M Z amp omega C₁ D₁ C₂ D₂ U ≤
        M*Cycle62.Arithmetic.g cell+6*amp+omega+supportPadding N b s.b₁ s.b₂ Z := by
  let v := commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂
  let X := Cycle62.Physical.sourcePlainScales v.toSource second
  have hx₁ := Cycle62Moment.LowBranch.source_plain_positive v second 0
  have hx₂ := Cycle62Moment.LowBranch.source_plain_positive v second 1
  have hprod : X 0*X 1=v.X₁*v.X₂ := by
    cases second
    · rfl
    · exact v.same_product
  have hb := actual_final_capacity_right N b hb s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ D₂ R₂ B₂ hf₂
    D₁ hD₁ hC₂ hD₂ hCD₂ U L a Z M amp omega hZ hM hP hz haffine
    (X 0) (X 1) hx₁ hx₂ hprod z hne
  have he : length Z (Cycle62Moment.LowBranch.finalPlain v second L a 0)+
      length Z (Cycle62Moment.LowBranch.finalPlain v second L a 1) =
        plainLogs L a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (clippedScale (rawScale L a (X 0) 0)))+
      Real.logb Z (max 1 (clippedScale (rawScale L a (X 1) 1))) = _
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]
    rfl
  dsimp only at hb ⊢
  rw [he]
  exact hb


#print axioms child_with_height
#print axioms actual_final_source_capacity
#print axioms actual_final_source_capacity_right
end
end OAI.SevenEighths.Cycle62FinalCapacity
