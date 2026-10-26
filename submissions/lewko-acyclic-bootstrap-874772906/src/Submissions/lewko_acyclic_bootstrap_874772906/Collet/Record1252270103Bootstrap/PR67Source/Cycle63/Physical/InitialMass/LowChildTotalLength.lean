import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowGeometry
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The total length of a live final row of a LOW child, plain lengths and slots at the same weight, is at most the log
volume of the parent less the log norms of the two extracted ideals. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
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

/-- The plain logs and the residual slot logs of an actual surviving residual row, at the same weight, are paid by
its genuine raw volume and the fixed plain-support clipping cost. -/
theorem supported_residual_total_length (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (Z : ℝ) (hZ : 1 < Z)
    (hP : ∀i,1 ≤ s.P i) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=s.X₁*s.X₂) (z : O)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P L a
      s.W₁ s.W₂ X₁ X₂ ≠ 0) :
    plainLogs L a Z X₁ X₂+remainingLogs L a Z s.P ≤
      Real.logb Z (preVolume s)+Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s L a z X₁ X₂ hX₁ hX₂ hne
  have hc := (clipping_loss_bound Z _ _ s.b₁ s.b₂ hZ
    (rawScale_pos L a X₁ hX₁ 0) (rawScale_pos L a X₂ hX₂ 1) hs₁ hs₂).2
  have hr := Real.logb_nonneg hZ (formalReduction_ge_one L a s.P hP)
  have he := affine_exact L a Z X₁ X₂ (1/6) 0 hZ hX₁ hX₂ s.P s.P_pos
  rw [hprod] at he
  change _ = Real.logb Z (preVolume s)-_ - _ + _ + _ at he
  linarith

/-- Two actual common allocations: the plain logs and the residual slot logs of a surviving row, at the same weight,
are paid by the volume of the parent less the raw reductions of the two common parts. -/
theorem two_stage_total_length (s : Input ι) (C₁ R₁ : Ideal O)
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
    plainLogs L a Z X₁ X₂+remainingLogs L a Z final.P ≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
        Real.logb Z (rawReduction B₂.val first.P)+Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  let first := child s C₁ R₁ B₁ χ t
  let final := commonData first C₂ R₂ B₂
  have hp₁ : ∀i,1 ≤ first.P i := fun i => hP i.val
  have hp₂ : ∀i,1 ≤ final.P i := fun i => hp₁ i.val
  have hb := supported_residual_total_length final L a Z hZ hp₂ X₁ X₂ hX₁ hX₂ hprod z hne
  have hv : Real.logb Z (preVolume final) = Real.logb Z (preVolume s.toData)-
      Real.logb Z (rawReduction B₁.val s.P)-Real.logb Z (rawReduction B₂.val first.P) := by
    rw [common_preVolume,Real.logb_div (preVolume_pos first.toData).ne'
      (rawReduction_pos B₂.val (alloc_ne first C₂ B₂) first.P first.P_pos).ne',
      first_child_prevolume,Real.logb_div (preVolume_pos s.toData).ne'
      (rawReduction_pos B₁.val (alloc_ne s C₁ B₁) s.P s.P_pos).ne']
  rw [hv] at hb
  change _ ≤ _ at hb ⊢
  change plainLogs L a Z X₁ X₂+remainingLogs L a Z final.P ≤ _ + Real.logb Z (max 1 final.b₁*max 1 final.b₂) at hb
  exact hb

end
end OAI.SevenEighths.Cycle63FinalCapacity

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle63FinalLow
open Cycle63FinalNatural Cycle63FinalCapacity
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The total plain length of a live final row, with its slot length at the same weight, is at most the log volume of
the parent less the log norms of its own first ideal and of its own second ideal, up to the support padding. -/
theorem live_main_total_length {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b : ℝ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b (Fintype.card α)) (hb : 1≤b)
    (hs : s.upper≤b) (hZ : 1<Z) (hP : ∀j,1≤ s.P j)
    (η : Character) (v : ℝ) (second : Bool) (L₂ : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L₂ (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L₂ a z≠0) :
    CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)+
        CenteredMomentAllocatedChildCapacity.remainingLogs L₂ a Z (q.final η v).P ≤
      Real.logb Z (volume s)-Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (q.E₂.absNorm:ℝ)+
        supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  let X := Cycle63.Physical.sourcePlainScales (q.final η v).toSource second
  have hp : X 0*X 1=(q.final η v).X₁*(q.final η v).X₂ := by
    cases second; rfl; exact (q.final η v).same_product
  have ht := two_stage_total_length s q.C₁ q.R₁ q.B₁ η v q.E₂ q.R₂ q.B₂ L₂ a Z hZ hP
    (X 0) (X 1) (Cycle63Moment.LowBranch.source_plain_positive _ second 0)
    (Cycle63Moment.LowBranch.source_plain_positive _ second 1) hp z hne
  have hr₁ := common_reduction_log_lower (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁ g.first_nonzero Z hZ
  have hr₂ := common_reduction_log_lower (Fintype.card α) b hb q.first (live_card_le q.B₁.val) hs
    q.E₂ q.R₂ q.B₂ g.second_nonzero Z hZ
  have he : CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)=
      CenteredMomentAllocatedChildCapacity.plainLogs L₂ a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))=_
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]; rfl
  dsimp only at ht
  rw [he]; unfold supportPadding
  change _≤_ at ht hr₂
  dsimp only [Chain.first,Chain.final,CenteredMomentCommonRadialData.commonData,
    CenteredMomentCommonHeightEnvelope.withHeight,CenteredMomentAmplificationChildInput.child] at ht hr₂ ⊢
  change _ ≤ Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume s.toData) - _ - _ + _
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
