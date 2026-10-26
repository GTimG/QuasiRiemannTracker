/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualSlotLoss
import Candidate.Research.RecursiveAffine.ActualCoordinateLift
import Candidate.Research.RecursiveAffine.PhysicalRetainedCaps

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentAllocatedNaturalSource
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands
open CenteredMomentEnergyInputParentCapacity
open Cycle63FinalLow Cycle63Moment.LowBranch Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual daughter capacity after the attaining whole-slot deletion,
in the exact original ray dictionary of the energy source. Both common
norms and the same residual F are paid, with the literal source support
padding. A capacity upper bound is not redefined as a daughter length. -/
theorem actual_deleted_daughter_total_capacity
    (s : Input ι) (ch : Chain s) (χ : Character) (t Z : ℝ)
    (hZ : 1 < Z) (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (hP : ∀ i, 1 ≤ s.P i) (w : ι → ℝ) (hscale : ∀ i, s.P i = Z ^ w i)
    (hn₁ : frozenCoefficient ch.B₁.val ch.C₁ ch.R₁ s.ν s.W s.P ≠ 0)
    (hn₂ : frozenCoefficient ch.B₂.val ch.E₂ ch.R₂
      ch.first.ν ch.first.W ch.first.P ≠ 0)
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val) ⊕ Fin 2)))
    (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L a z ≠ 0)
    (Rdel : Finset ι) (hRdel : Rdel ⊆ ch.indices L a) :
    length Z (rawDaughterScale (ch.final χ t) second L a 0) +
      length Z (rawDaughterScale (ch.final χ t) second L a 1) +
      (∑ i ∈ ch.indices L a \ Rdel, w i) ≤
    (length Z s.X₁ + length Z s.X₂ + ∑ i, w i) - (∑ i ∈ Rdel, w i) -
      Real.logb Z (ch.C₁.absNorm : ℝ) - Real.logb Z (ch.E₂.absNorm : ℝ) -
      Real.logb Z (formalReductionFactor L a (ch.final χ t).P) +
      (2 * (N : ℝ) * Real.logb Z b + Real.logb Z (max 1 s.b₁ * max 1 s.b₂)) := by
  let src := ch.final χ t
  let X := Cycle63.Physical.sourcePlainScales src.toSource second
  have hprod : X 0 * X 1 = src.X₁ * src.X₂ := by
    cases second
    · rfl
    · exact src.same_product
  have hcap := Cycle153PhysicalCapacity.two_stage_common_norm_capacity
    s N b hb hcard hs ch.C₁ ch.R₁ ch.B₁ χ t ch.E₂ ch.R₂ ch.B₂ hn₁ hn₂ L a Z (1/6) 0
    hZ le_rfl hP (X 0) (X 1) (source_plain_scale_pos src second 0)
      (source_plain_scale_pos src second 1) hprod z hne
  have hplain : length Z (rawDaughterScale src second L a 0) +
      length Z (rawDaughterScale src second L a 1) = plainLogs L a Z (X 0) (X 1) := by
    rfl
  have hslots := original_slot_sum s ch χ t Z hZ w hscale L a
  have hsum : (∑ i, Real.logb Z (s.P i)) = ∑ i, w i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hscale i, Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hdel : (∑ i ∈ ch.indices L a \ Rdel, w i) + (∑ i ∈ Rdel, w i) =
      ∑ i ∈ ch.indices L a, w i := Finset.sum_sdiff hRdel
  have hpre : Real.logb Z (preVolume s.toData) ≤
      length Z s.X₁ + length Z s.X₂ + ∑ i, w i := by
    change Real.logb Z (volume s) ≤ _
    rw [input_volume_log, hsum]
    linarith only [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
      raw_log_le_length Z s.X₂ hZ s.X₂_pos]
  dsimp only at hcap
  change plainLogs L a Z (X 0) (X 1) + 6 * (1/6 : ℝ) * remainingLogs L a Z src.P - 0 ≤ _ at hcap
  norm_num at hcap
  change length Z (rawDaughterScale src second L a 0) +
      length Z (rawDaughterScale src second L a 1) + _ ≤ _
  rw [hplain]
  change remainingLogs L a Z src.P = _ at hslots
  rw [hslots] at hcap
  change plainLogs L a Z (X 0) (X 1) + (∑ i ∈ ch.indices L a, w i) ≤
    Real.logb Z (preVolume s.toData) - Real.logb Z (ch.C₁.absNorm : ℝ) -
      Real.logb Z (ch.E₂.absNorm : ℝ) - Real.logb Z (formalReductionFactor L a src.P) +
      (2 * (N : ℝ) * Real.logb Z b + Real.logb Z (max 1 s.b₁ * max 1 s.b₂)) at hcap
  change _ ≤ _ - Real.logb Z (ch.C₁.absNorm : ℝ) - Real.logb Z (ch.E₂.absNorm : ℝ) -
    Real.logb Z (formalReductionFactor L a src.P) + _
  linarith only [hcap, hpre, hdel]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_deleted_daughter_total_capacity
