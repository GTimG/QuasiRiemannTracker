import Candidate.Research.RecursiveAffine.RetainedFDaughter
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle152RetainedFReturn
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentAllocatedNaturalSource
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal two-common-stage capacity, retaining the residual formal
reduction in the general weighted old-gap cap. No candidate callback or
assumed returned-length field enters this source estimate. -/
theorem two_stage_affine_capacity_retained_F (s : Input ι) (C₁ R₁ : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (χ : Character) (t : ℝ)
    (C₂ R₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z κ nominal : ℝ) (hZ : 1 < Z) (hκ : (1 / 6 : ℝ) ≤ κ)
    (hP : ∀ i, 1 ≤ s.P i)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁ * X₂ = (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₁ *
      (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₂)
    (z : O) (hne : let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
      allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P L a
        v.W₁ v.W₂ X₁ X₂ ≠ 0) :
    let first := child s C₁ R₁ B₁ χ t
    let final := commonData first C₂ R₂ B₂
    plainLogs L a Z X₁ X₂ + 6 * κ * remainingLogs L a Z final.P - nominal ≤
      Real.logb Z (preVolume s.toData) - Real.logb Z (rawReduction B₁.val s.P) -
        Real.logb Z (rawReduction B₂.val first.P) -
        Real.logb Z (formalReductionFactor L a final.P) - nominal +
        (6 * κ - 1) * (∑ i, Real.logb Z (s.P i)) +
        Real.logb Z (max 1 s.b₁ * max 1 s.b₂) := by
  let first := child s C₁ R₁ B₁ χ t
  let final := commonData first C₂ R₂ B₂
  have hp₁ : ∀ i, 1 ≤ first.P i := fun i => hP i.val
  have hp₂ : ∀ i, 1 ≤ final.P i := fun i => hp₁ i.val
  have hc := Cycle151RetainedF.supported_residual_total_length_retained
    final L a Z hZ X₁ X₂ hX₁ hX₂ hprod z hne
  have hfirst : preVolume first.toData =
      preVolume s.toData / rawReduction B₁.val s.P := by
    change preVolume (commonData s C₁ R₁ B₁) = _
    exact common_preVolume s C₁ R₁ B₁
  have hv : Real.logb Z (preVolume final) = Real.logb Z (preVolume s.toData) -
      Real.logb Z (rawReduction B₁.val s.P) - Real.logb Z (rawReduction B₂.val first.P) := by
    rw [common_preVolume, Real.logb_div (preVolume_pos first.toData).ne'
      (rawReduction_pos B₂.val (alloc_ne first C₂ B₂) first.P first.P_pos).ne',
      hfirst, Real.logb_div (preVolume_pos s.toData).ne'
      (rawReduction_pos B₁.val (alloc_ne s C₁ B₁) s.P s.P_pos).ne']
  rw [hv] at hc
  have hr := remainingLogs_le L a Z hZ final.P hp₂
  have hs₂ := common_slot_logs_le first C₂ B₂ Z hZ hp₁
  have hs₁ := common_slot_logs_le s C₁ B₁ Z hZ hP
  have hslots : remainingLogs L a Z final.P ≤ ∑ i, Real.logb Z (s.P i) :=
    hr.trans (hs₂.trans hs₁)
  have hw := mul_le_mul_of_nonneg_left hslots
    (by linarith only [hκ] : 0 ≤ 6 * κ - 1)
  change _ ≤ _ + Real.logb Z (max 1 s.b₁ * max 1 s.b₂) at hc
  change _ ≤ _
  nlinarith only [hc, hw]

end
end OAI.SevenEighths.Cycle152RetainedFReturn

#print axioms OAI.SevenEighths.Cycle152RetainedFReturn.two_stage_affine_capacity_retained_F
