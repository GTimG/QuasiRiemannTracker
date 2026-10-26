import Candidate.Target836.SourceProvider.CellGeometry
import Candidate.Cycle63.Physical.FinalCapacity.Final
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
import Candidate.Cycle63.Physical.FinalCapacity.Allocation
import Candidate.Cycle63.Physical.FinalCapacity.Geometry
import Candidate.Cycle63.Physical.InitialMass.SecondLowGeometry
import Candidate.Cycle63.Physical.InitialMass.SecondOrientedWidth
import Candidate.Cycle63.Physical.InitialMass.SecondLowUniform
import Candidate.Target836.SourceProvider.LowPaidMain

/- Original module: Candidate.Target836.SourceProvider.OriginalCapacity. -/
section

set_option autoImplicit false
namespace Target874836.SourceProvider.FinalCapacity
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
variable {ι : Type*} [Fintype ι]

/-- The original affine cell, rather than an old parent-capacity gate, pays
the old 9/2 final capacity. Raw logarithms are bounded by clamped lengths. -/
theorem original_affine_capacity (s : Input ι) (Z M : ℝ) (hZ : 1 < Z) (hM : 0 < M)
    (hz : (17/500)*M ≤ ∑ i, Real.logb Z (s.P i) ∧
      (∑ i, Real.logb Z (s.P i)) ≤ (1/25)*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Named.lam*(∑ i, Real.logb Z (s.P i)) ≤ Named.B*M) :
    let b := Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑ i,Real.logb Z (s.P i))/M))
    Real.logb Z (volume s)+(6*incumbentKappa-1)*(∑ i,Real.logb Z (s.P i)) ≤ M+M*Named.gap b := by
  dsimp only
  obtain ⟨_,_,hcap,_,_⟩ := Target874836.SourceProvider.normalized_cell_bounds hM hz haffine
  have hh := (le_max_left (length Z s.X₁+length Z s.X₂+
    (6*incumbentKappa)*(∑ i,Real.logb Z (s.P i))-M) 0).trans hcap
  rw [input_volume_log]
  linarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

#print axioms original_affine_capacity
end
end Target874836.SourceProvider.FinalCapacity
end

/- Original module: Candidate.Target836.SourceProvider.SupportedCapacity. -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Target874836.SourceProvider.FinalCapacity
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalCapacity
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
    plainLogs L a Z X₁ X₂+(6*incumbentKappa)*remainingLogs L a Z s.P ≤
      Real.logb Z (preVolume s)+(6*incumbentKappa-1)*(∑i,Real.logb Z (s.P i))+
        Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s L a z X₁ X₂ hX₁ hX₂ hne
  have hc := (clipping_loss_bound Z _ _ s.b₁ s.b₂ hZ
    (rawScale_pos L a X₁ hX₁ 0) (rawScale_pos L a X₂ hX₂ 1) hs₁ hs₂).2
  have hl := remainingLogs_le L a Z hZ s.P hP
  have hr := Real.logb_nonneg hZ (formalReduction_ge_one L a s.P hP)
  have he := affine_exact L a Z X₁ X₂ incumbentKappa 0 hZ hX₁ hX₂ s.P s.P_pos
  rw [hprod] at he
  change _ = Real.logb Z (preVolume s)-_ - _ + _ + _ at he
  norm_num [incumbentKappa] at *
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
    plainLogs L a Z X₁ X₂+(6*incumbentKappa)*remainingLogs L a Z final.P ≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (rawReduction B₁.val s.P)-
        Real.logb Z (rawReduction B₂.val first.P)+(6*incumbentKappa-1)*(∑i,Real.logb Z (s.P i))+
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
    Real.logb Z (rawReduction B₂.val first.P)+(6*incumbentKappa-1)*(∑i,Real.logb Z (final.P i))+
      Real.logb Z (max 1 s.b₁*max 1 s.b₂) at hb
  norm_num [incumbentKappa] at *
  linarith

#print axioms supported_residual_capacity
#print axioms two_stage_supported_capacity
end
end Target874836.SourceProvider.FinalCapacity
end

/- Original module: Candidate.Target836.SourceProvider.FinalCapacity. -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Target874836.SourceProvider.FinalCapacity
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalCapacity
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
      Named.lam*(∑i,Real.logb Z (s.P i)) ≤ Named.B*M)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=(commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₁*
      (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₂)
    (z : O) (hne : let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
      allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P L a
        v.W₁ v.W₂ X₁ X₂ ≠ 0) :
    let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
    let cell := Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))
    plainLogs L a Z X₁ X₂+(6*incumbentKappa)*remainingLogs L a Z v.P-
      secondNominal M Z amp omega C₁ D₁ C₂ D₂ U ≤
        M*Named.gap cell+6*amp+omega+supportPadding N b s.b₁ s.b₂ Z := by
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
  change Real.logb Z (preVolume s.toData)+(6*incumbentKappa-1)*(∑i,Real.logb Z (s.P i)) ≤ _ at hcell
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
      Named.lam*(∑i,Real.logb Z (s.P i)) ≤ Named.B*M)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂=(commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂).X₁*
      (commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂).X₂)
    (z : O) (hne : let v := commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂
      allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P L a
        v.W₁ v.W₂ X₁ X₂ ≠ 0) :
    let v := commonData (child s C₁ R₁ B₁ χ t) D₂ R₂ B₂
    let cell := Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))
    plainLogs L a Z X₁ X₂+(6*incumbentKappa)*remainingLogs L a Z v.P-
      secondNominal M Z amp omega C₁ D₁ C₂ D₂ U ≤
        M*Named.gap cell+6*amp+omega+supportPadding N b s.b₁ s.b₂ Z := by
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
  change Real.logb Z (preVolume s.toData)+(6*incumbentKappa-1)*(∑i,Real.logb Z (s.P i)) ≤ _ at hcell
  unfold secondNominal supportPadding
  linarith


#print axioms actual_final_capacity
#print axioms actual_final_capacity_right
end
end Target874836.SourceProvider.FinalCapacity
end

/- Original module: Candidate.Target836.SourceProvider.LiveCapacity. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Target874836.SourceProvider.Physical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle63FinalLow
open Cycle63FinalNatural Cycle63FinalCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem live_main_source_capacity {s : OAI.SevenEighths.CenteredMomentCommonRadialData.Input α} {q : OAI.SevenEighths.Cycle63FinalLow.Chain s} {Z Mrow amp omega ξ b : ℝ}
    (g : LiveMainGeometry s q Z Mrow amp omega ξ b (Fintype.card α)) (hb : 1 ≤ b)
    (hs : s.upper ≤ b) (hZ : 1< Z) (hM : 0< Mrow) (hP : ∀j,1 ≤ s.P j)
    (hz : (17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Named.lam*(∑j,Real.logb Z (s.P j)) ≤ Named.B*Mrow)
    (η : Character) (v : ℝ) (second : Bool) (L₂ : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L₂ (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L₂ a z≠0) :
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)+
        (6*incumbentKappa)*CenteredMomentAllocatedChildCapacity.remainingLogs L₂ a Z (q.final η v).P-
        secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive  ≤ 
      Mrow*Named.gap cell+6*amp+omega+supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  have shift : Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D))-
      Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ) ≤ Real.logb Z (q.E₂.absNorm:ℝ) := by
    rcases g.label with h|h
    · rw [h]; exact actual_common_shift_le g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
    · rw [h]; exact actual_common_shift_le_right g.datum.C g.datum.D g.datum.hC g.datum.hD g.datum.sameSupport g.datum.inactive Z hZ
  let X := Cycle63.Physical.sourcePlainScales (q.final η v).toSource second
  have hp : X 0*X 1=(q.final η v).X₁*(q.final η v).X₂ := by
    cases second; rfl; exact (q.final η v).same_product
  have ht := Target874836.SourceProvider.FinalCapacity.two_stage_supported_capacity s q.C₁ q.R₁ q.B₁ η v q.E₂ q.R₂ q.B₂ L₂ a Z hZ hP
    (X 0) (X 1) (Cycle63Moment.LowBranch.source_plain_positive _ second 0)
    (Cycle63Moment.LowBranch.source_plain_positive _ second 1) hp z hne
  have hr₁ := common_reduction_log_lower (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁ g.first_nonzero Z hZ
  have hr₂ := common_reduction_log_lower (Fintype.card α) b hb q.first (live_card_le q.B₁.val) hs
    q.E₂ q.R₂ q.B₂ g.second_nonzero Z hZ
  have hc := Target874836.SourceProvider.FinalCapacity.original_affine_capacity s Z Mrow hZ hM hz haff
  have hm : max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0 ≤ Real.logb Z (q.C₁.absNorm:ℝ) :=
    max_le (sub_le_self _ (Real.logb_nonneg hZ (norm_ge_one _ g.hD₁.1)))
      (Real.logb_nonneg hZ (norm_ge_one _ g.hC₁.1))
  have he : CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L₂ a 1)=
      CenteredMomentAllocatedChildCapacity.plainLogs L₂ a Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))=_
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]; rfl
  dsimp only at hc ht ⊢
  rw [he]; unfold secondNominal supportPadding
  change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume s.toData)+(6*incumbentKappa-1)*(∑j,Real.logb Z (s.P j)) ≤ _ at hc
  change _ ≤ _ at ht hr₂
  dsimp only [Chain.first,Chain.final,CenteredMomentCommonRadialData.commonData,
    CenteredMomentCommonHeightEnvelope.withHeight,CenteredMomentAmplificationChildInput.child] at ht hr₂ ⊢
  linarith

end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.live_main_source_capacity
end

/- Original module: Candidate.Target836.SourceProvider.LiveLowUniform. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Target874836.SourceProvider.Physical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Actual main second low energy. Constants are chosen on the original
 ambient labels before either common allocation, all rows and all heights. -/
theorem actual_live_main_low_uniform
    (W : ℝ→ℂ) (A B ap bp Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (hap : 0 < ap) (hap' : ap ≤ 1/4) (hbp : 1 ≤ bp)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs bp₁ bp₂ εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q ≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0 < Cg ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀(hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper ≤ bs → s.b₁=bp₁ → s.b₂=bp₂ →
      (∀j,0 ≤ w j) → (∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d ≤ Rwidth) → 0 ≤ mesh → (∀j,w j ≤ mesh) → (∀j,lo ≤ σ j) → (∀j,σ j ≤ hi) →
      0 ≤ height → (∀j,|freq j| ≤ height) → 51/100 ≤ aLow → aLow ≤ ((1+Named.q)/2) →
      |v|+height+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin ≤ Mrow → 0 ≤ omega → 0 ≤ ξ → Mrow+εwidth*Mrow+ξ/2 ≤ Mcap →
      ((17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Named.lam*(∑j,Real.logb Z (s.P j)) ≤ Named.B*Mrow →
    ∀q : Chain s,
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Named.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ) ≤ Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := q.final (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p : Profiles ap bp,
      dilated s.W₁ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 0/
        (Ideal.absNorm (selectedPlain L₂ alloc 0):ℝ)))=p.profile 0 →
      dilated s.W₂ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 1/
        (Ideal.absNorm (selectedPlain L₂ alloc 1):ℝ)))=p.profile 1 →
      finalPlain src second L₂ alloc 0 ≤ Z^L → finalPlain src second L₂ alloc 1 ≤ Z^L →
    let hQM' : st.fixedModulus ≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus ≤ η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=> st.radial.keep z ∧ low z) st.radial.profile st.radial.scale ≤ 
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-Mrow*Named.lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
          (Named.q/(6*incumbentKappa))*padding+Named.q*mesh) := by
  obtain ⟨degree,Sp,hmain⟩ := Target874836.SourceProvider.LowBranch.actual_paid_low_main (α:=α) M H hH W A B ap bp 2 Bmask L lo hi Mcap εold
    hA hWs hW hB hap hap' hbp (by norm_num) hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C^(Fintype.card α)*(C₀+C₁),by positivity,?_⟩
  filter_upwards [hbound,Cycle63FinalRadius.fixed_final_width_loss_uniform (fun _:Unit=>ηseed)
    (Fintype.card α) bs 1 εwidth Mmin (zero_lt_one.trans_le hbs) (by norm_num) hew hmin,
    support_padding_eventually_mass (Fintype.card α) bs bp₁ bp₂ εpad Mmin (zero_lt_one.trans_le hbs) hep hmin]
    with Z hZ hwidthLoss hpadLoss
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p hp₁ hp₂ hXcap₁ hXcap₂
  dsimp only
  have hM : 0 < Mrow := hmin.trans_le hMmin
  obtain ⟨hc₁,hc₂,_,_⟩ := Cycle63.Moment.originalCell_mem
    (show (17/500:ℝ) ≤ (∑j,Real.logb Z (s.P j))/Mrow ∧ (∑j,Real.logb Z (s.P j))/Mrow ≤ 1/25 from
      ⟨(le_div_iff₀ hM).mpr hz.1,(div_le_iff₀ hM).mpr hz.2⟩)
  have hcell := Cycle63.Arithmetic.cellUpper_bounds hc₁ hc₂
  have hamp := (mul_pos hM (show 0 < Named.amp cell by
        have hg : 0 < Named.gap cell := by norm_num [Named.gap,Named.B,Named.lam,Named.kappa,incumbentKappa] at *; linarith [hcell.1]
        unfold Named.amp Named.K Named.extra
        have hq : 0 < Named.q/(6*(Named.kappa-Named.q)) := by norm_num [Named.q,Named.kappa,incumbentKappa]
        have he : 0 < Named.lowReserve/(1-Named.q/Named.kappa) := by norm_num [Named.lowReserve,Named.q,Named.kappa,incumbentKappa]
        positivity)).le
  have hshift := CenteredMomentSecondActualWidth.actual_common_log_ge_unit g.datum.C g.datum.D g.datum.hC g.datum.inactive Z hZone
  have hnmax : 0 ≤ max (Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (g.D₁.absNorm:ℝ)) 0 := le_max_right _ _
  have hnominal : nominal ≤ Mrow := by unfold nominal secondNominal; linarith
  have hwidth : st.width-nominal ≤ δwidth := by
    have ht := live_main_state_width g Bmask hZone (zero_lt_one.trans_le hbs) χ (internalQ Q η₀) hP hPN
    have hl := hwidthLoss.2 () Mrow hMmin
    rw [←hsη] at hl
    norm_num only [Real.logb_one] at hl
    change st.width ≤ nominal+_ at ht
    dsimp [δwidth]; linarith
  have hδ : 0 ≤ δwidth := by dsimp [δwidth]; positivity
  have hpadding : 0 ≤ padding := by dsimp [padding]; positivity
  have hs : st.width ≤ Mcap := by dsimp only [δwidth] at hwidth; linarith
  by_cases live : ∃z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0
  · obtain ⟨z,hzrow⟩ := live
    have htotal := live_main_source_capacity g hbs hsupper hZone hM
      (fun j=> by rw [hm.scale j]; exact Real.one_le_rpow hZone.le (hw j)) hz haff (g.datum.τ χ) v second L₂ alloc z hzrow
    rw [original_slot_sum s q (g.datum.τ χ) v Z hZone w hm.scale L₂ alloc] at htotal
    have hpadd := hpadLoss.2 Mrow hMmin
    rw [←hsb₁,←hsb₂] at hpadd
    have htotal' : length Z (finalPlain src second L₂ alloc 0)+length Z (finalPlain src second L₂ alloc 1)+
        (6*incumbentKappa)*(∑j∈q.indices L₂ alloc,w j)-nominal ≤ Mrow*Named.gap cell+6*amp+padding := by
      change _ ≤ _ at htotal; dsimp [padding]; linarith
    obtain ⟨R,hR,hpaid,henergy⟩ := hZ.2 (q.indices L₂ alloc) θ w σ freq v height mesh aLow i hw hwL
      (fun j _=> hwr j) hmesh (fun j _=> hwm j) hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh
      st rfl hs p _ _ (zero_lt_one.trans_le (clippedScale_ge_one _))
      (zero_lt_one.trans_le (clippedScale_ge_one _)) hXcap₁ hXcap₂ cell Mrow nominal δwidth padding
      hcell hM.le hwidth hδ hpadding htotal'
    rw [original_low_energy M H hH s η₀ θ w σ freq W B Z Bmask hZone hm q (g.datum.τ χ) v
      (internalQ Q η₀) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive second L₂ alloc _,hp₁,hp₂]
    exact henergy.trans_eq (by ring)
  · have hzrow : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      simpa only [not_exists,not_not] using live
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms Target874836.SourceProvider.Physical.actual_live_main_low_uniform
end
end Target874836.SourceProvider.Physical
end
