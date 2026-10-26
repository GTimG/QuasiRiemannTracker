/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainParameters
import Candidate.Cycle63.Physical.FinalCapacity.Allocation
import Candidate.Cycle63.Physical.FinalCapacity.Affine
import Candidate.Cycle63.Physical.FinalCapacity.Geometry

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.MainCapacity
noncomputable section
open Sil.Uneven.MainSource
variable (P : Plane)
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
open Cycle63FinalCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The current-incumbent capacity of an actual surviving residual row is paid by
 its genuine raw volume and the fixed plain-support clipping cost. -/
theorem supported_residual_capacity (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (hP : ∀i,1 ≤ s.P i) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=s.X₁*s.X₂) (z : O)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P L a
      s.W₁ s.W₂ X₁ X₂ ≠ 0) :
    plainLogs L a Z X₁ X₂+(6*P.incumbent)*remainingLogs L a Z s.P ≤
      Real.logb Z (preVolume s)+(6*P.incumbent-1)*(∑i,Real.logb Z (s.P i))+
        Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s L a z X₁ X₂ hX₁ hX₂ hne
  have hc := (clipping_loss_bound Z _ _ s.b₁ s.b₂ hZ
    (rawScale_pos L a X₁ hX₁ 0) (rawScale_pos L a X₂ hX₂ 1) hs₁ hs₂).2
  have hl := remainingLogs_le L a Z hZ s.P hP
  have hr := Real.logb_nonneg hZ (formalReduction_ge_one L a s.P hP)
  have he := affine_exact L a Z X₁ X₂ P.incumbent 0 hZ hX₁ hX₂ s.P s.P_pos
  rw [hprod] at he
  change _ = Real.logb Z (preVolume s)-_ - _ + _ + _ at he
  cases P <;> norm_num [Plane.incumbent] at * <;> linarith

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
    plainLogs L a Z X₁ X₂+(6*P.incumbent)*remainingLogs L a Z final.P ≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
        Real.logb Z (rawReduction B₂.val first.P)+(6*P.incumbent-1)*(∑i,Real.logb Z (s.P i))+
        Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  let first := child s C₁ R₁ B₁ χ t
  let final := commonData first C₂ R₂ B₂
  have hp₁ : ∀i,1 ≤ first.P i := fun i => hP i.val
  have hp₂ : ∀i,1 ≤ final.P i := fun i => hp₁ i.val
  have hb := supported_residual_capacity P final L a Z hZ hp₂ X₁ X₂ hX₁ hX₂ hprod z hne
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
    Real.logb Z (rawReduction B₂.val first.P)+(6*P.incumbent-1)*(∑i,Real.logb Z (final.P i))+
      Real.logb Z (max 1 s.b₁*max 1 s.b₂) at hb
  cases P <;> norm_num [Plane.incumbent] at * <;> linarith

end
end OAI.SevenEighths.MainCapacity
