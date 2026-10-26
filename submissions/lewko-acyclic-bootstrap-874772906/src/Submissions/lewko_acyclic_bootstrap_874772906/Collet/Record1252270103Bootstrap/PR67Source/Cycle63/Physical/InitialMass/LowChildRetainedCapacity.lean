import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowGeometry
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- A live LOW child keeps the extraction reductions of its two common allocations in its source capacity.
Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
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

/-- The total plain length of a live final row, with its slot capacity, exceeds the nominal width of the child by at
most the capacity of the parent's cell and the padding, less the extraction reductions that the child keeps: the
smaller of the two first ideals, and the part of the second common ideal beyond the shift of its nonunit frequency
generator. Here `unit` is the ledger unit of the parent and `Mrow` the radial scale of the child. -/
theorem live_main_source_capacity_retained {s : Input α} {q : Chain s} {Z unit Mrow amp omega ξ b : ℝ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b (Fintype.card α)) (hb : 1≤b)
    (hs : s.upper≤b) (hZ : 1<Z) (hunit : 0<unit) (hP : ∀j,1≤ s.P j)
    (hz : Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit)
    (η : Character) (v : ℝ) (second : Bool) (L₂ : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L₂ (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L₂ a z≠0) :
    let cell := Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)+
        (6*Cycle63.Optimization.slotPrice)*CenteredMomentAllocatedChildCapacity.remainingLogs L₂ a Z (q.final η v).P-
        secondNominal unit Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive ≤
      unit*Cycle63.AffineLedger.g cell+6*amp+omega+supportPadding (Fintype.card α) b s.b₁ s.b₂ Z-
        (min (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
          (Real.logb Z (q.E₂.absNorm:ℝ)-
            (Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
              Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ)))) := by
  have shift : Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
      Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ)≤Real.logb Z (q.E₂.absNorm:ℝ) := by
    rcases g.label with h|h
    · rw [h]; exact actual_common_shift_le g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
    · rw [h]; exact actual_common_shift_le_right g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
  let X := Cycle63.Physical.sourcePlainScales (q.final η v).toSource second
  have hp : X 0*X 1=(q.final η v).X₁*(q.final η v).X₂ := by
    cases second; rfl; exact (q.final η v).same_product
  have ht := two_stage_supported_capacity s q.C₁ q.R₁ q.B₁ η v q.E₂ q.R₂ q.B₂ L₂ a Z hZ hP
    (X 0) (X 1) (Cycle63Moment.LowBranch.source_plain_positive _ second 0)
    (Cycle63Moment.LowBranch.source_plain_positive _ second 1) hp z hne
  have hr₁ := common_reduction_log_lower (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁ g.first_nonzero Z hZ
  have hr₂ := common_reduction_log_lower (Fintype.card α) b hb q.first (live_card_le q.B₁.val) hs
    q.E₂ q.R₂ q.B₂ g.second_nonzero Z hZ
  have hc := original_affine_capacity s Z unit hZ hunit hz haff
  have hmm : min (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
      max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0=Real.logb Z (q.C₁.absNorm:ℝ) := by
    rcases le_total (Real.logb Z (q.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ)) with h|h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have he : CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)=
      CenteredMomentAllocatedChildCapacity.plainLogs L₂ a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))=_
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]; rfl
  dsimp only at hc ht ⊢
  rw [he]; unfold secondNominal supportPadding
  change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume s.toData)+(6*Cycle63.Optimization.slotPrice-1)*(∑j,Real.logb Z (s.P j))≤_ at hc
  change _≤_ at ht hr₂
  dsimp only [Chain.first,Chain.final,CenteredMomentCommonRadialData.commonData,
    CenteredMomentCommonHeightEnvelope.withHeight,CenteredMomentAmplificationChildInput.child] at ht hr₂ ⊢
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
