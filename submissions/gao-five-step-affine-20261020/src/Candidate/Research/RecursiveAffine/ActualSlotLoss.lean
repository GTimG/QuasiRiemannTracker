/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalDaughterSource

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentAllocatedNaturalSource
open CenteredMomentSourceLiveColumn
open Cycle63FinalLow Cycle63Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The slot loss of a literal common allocation is paid by its raw
reduction. The plain part of the allocation can only increase that credit. -/
theorem actual_common_slot_loss_raw (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (Z : ℝ) (hZ : 1 < Z) :
    (∑ i, Real.logb Z (s.P i)) -
      (∑ i, Real.logb Z ((commonData s C R B).P i)) ≤
        Real.logb Z (rawReduction B.val s.P) := by
  have hf : 0 < ∏ i, frozenScale B.val s.P i :=
    Finset.prod_pos (fun i _ => frozenScale_pos B.val s.P s.P_pos i)
  have hl : 0 < ∏ i : CenteredMomentCommonProfile.liveIndices B.val, s.P i :=
    Finset.prod_pos (fun i _ => s.P_pos i.val)
  have hh := congrArg (Real.logb Z) (slot_scale_split B.val s.P)
  rw [Real.logb_mul hf.ne' hl.ne',
    Real.logb_prod _ _ (fun i _ => (frozenScale_pos B.val s.P s.P_pos i).ne'),
    Real.logb_prod _ _ (fun i _ => (s.P_pos i.val).ne'),
    Real.logb_prod _ _ (fun i _ => (s.P_pos i).ne')] at hh
  have hnorm : 1 ≤ plainNorm B.val := by
    unfold plainNorm
    apply one_le_mul_of_one_le_of_one_le <;>
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B _))
  have hn : 0 ≤ Real.logb Z (plainNorm B.val) := Real.logb_nonneg hZ hnorm
  rw [rawReduction, Real.logb_mul (plainNorm_pos B.val (alloc_ne s C B)).ne' hf.ne',
    Real.logb_prod _ _ (fun i _ => (frozenScale_pos B.val s.P s.P_pos i).ne')]
  change (∑ i, Real.logb Z (s.P i)) -
      (∑ i : CenteredMomentCommonProfile.liveIndices B.val, Real.logb Z (s.P i)) ≤ _
  linarith only [hh, hn]

/-- With the actual original slot support beginning at one, the same
nonzero common allocation's ideal norm pays its whole slot loss exactly.
The upper support constant is not used for this direction. -/
theorem actual_common_slot_loss_norm (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (Z : ℝ) (hZ : 1 < Z)
    (hlower : 1 ≤ s.lower)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0) :
    (∑ i, Real.logb Z (s.P i)) -
      (∑ i, Real.logb Z ((commonData s C R B).P i)) ≤
        Real.logb Z (C.absNorm : ℝ) := by
  have hraw := actual_common_slot_loss_raw s C R B Z hZ
  have hn := (actual_reduction_norm B.val (alloc_ne s C B) C R
    (allocation_product s C B) s.ν s.W s.P s.P_pos s.lower s.upper
    s.lower_pos s.slot_support hne).1
  rw [min_eq_left hlower, one_pow, one_mul] at hn
  exact hraw.trans (Real.logb_le_logb_of_le hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hn)

/-- Actual residual frozen slots are paid by their same allocation's
formal reduction F, with its selected plain ideal norms retained. -/
theorem actual_residual_slot_loss (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (Z : ℝ) (hZ : 1 < Z) (P : ι → ℝ) (hP : ∀ i, 0 < P i) :
    (∑ i, Real.logb Z (P i)) - remainingLogs L a Z P ≤
      Real.logb Z (formalReductionFactor L a P) := by
  have hf : 0 < ∏ i ∈ CenteredMomentDivisorRaw.frozenIndices L a, P i :=
    Finset.prod_pos (fun i _ => hP i)
  have hl : 0 < ∏ i ∈ CenteredMomentDivisorRaw.liveIndices L a, P i :=
    Finset.prod_pos (fun i _ => hP i)
  have hh := congrArg (Real.logb Z) (split_slot_product L a P)
  rw [Real.logb_mul hf.ne' hl.ne',
    Real.logb_prod _ _ (fun i _ => (hP i).ne'),
    Real.logb_prod _ _ (fun i _ => (hP i).ne'),
    Real.logb_prod _ _ (fun i _ => (hP i).ne')] at hh
  have hn : 0 ≤ Real.logb Z (selectedNorm L a) :=
    Real.logb_nonneg hZ (selectedNorm_ge_one L a)
  rw [formalReductionFactor, Real.logb_mul (selectedNorm_pos L a).ne' hf.ne',
    Real.logb_prod _ _ (fun i _ => (hP i).ne')]
  unfold remainingLogs
  linarith only [hh, hn]

/-- The exact slots discarded by both common allocations and a literal
residual allocation satisfy the physical model loss budget. This uses the
two common ideal norms and the SAME residual F as the checked daughter
capacity; no independently selected reduction is inserted. -/
theorem actual_two_common_residual_slot_loss (s : Input ι)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (χ : Character) (t : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
    (Z : ℝ) (hZ : 1 < Z) (hlower : 1 ≤ s.lower)
    (hP : ∀ i, 1 ≤ s.P i)
    (hn₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P ≠ 0)
    (hn₂ : frozenCoefficient B₂.val C₂ R₂
      (child s C₁ R₁ B₁ χ t).ν (child s C₁ R₁ B₁ χ t).W
      (child s C₁ R₁ B₁ χ t).P ≠ 0) :
    let final := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
    let ell := (∑ i, Real.logb Z (s.P i)) - remainingLogs L a Z final.P
    0 ≤ ell ∧ ell ≤ Real.logb Z (C₁.absNorm : ℝ) +
      Real.logb Z (C₂.absNorm : ℝ) +
      Real.logb Z (formalReductionFactor L a final.P) := by
  let first := child s C₁ R₁ B₁ χ t
  let final := commonData first C₂ R₂ B₂
  have h₁ := actual_common_slot_loss_norm s C₁ R₁ B₁ Z hZ hlower hn₁
  have h₂ := actual_common_slot_loss_norm first C₂ R₂ B₂ Z hZ hlower hn₂
  have h₃ := actual_residual_slot_loss L a Z hZ final.P final.P_pos
  have hP₁ : ∀ i, 1 ≤ first.P i := fun i => hP i.val
  have hP₂ : ∀ i, 1 ≤ final.P i := fun i => hP₁ i.val
  have hs₁ := common_slot_logs_le s C₁ B₁ Z hZ hP
  have hs₂ := common_slot_logs_le first C₂ B₂ Z hZ hP₁
  have hs₃ := remainingLogs_le L a Z hZ final.P hP₂
  change (∑ i, Real.logb Z (first.P i)) ≤ (∑ i, Real.logb Z (s.P i)) at hs₁
  change (∑ i, Real.logb Z (final.P i)) ≤ (∑ i, Real.logb Z (first.P i)) at hs₂
  change 0 ≤ (∑ i, Real.logb Z (s.P i)) - remainingLogs L a Z final.P ∧ _
  constructor
  · linarith only [hs₁, hs₂, hs₃]
  · change (∑ i, Real.logb Z (s.P i)) -
      (∑ i, Real.logb Z (first.P i)) ≤ _ at h₁
    change (∑ i, Real.logb Z (first.P i)) -
      (∑ i, Real.logb Z (final.P i)) ≤ _ at h₂
    linarith only [h₁, h₂, h₃]

/-- Source-level binding of the slot-loss coordinate to the literal
surviving original ray dictionary used by `actual_regional_daughter_source`.
The same physical chain and actual residual allocation determine J and F. -/
theorem actual_original_dictionary_slot_loss (s : Input ι) (ch : Chain s)
    (χ : Character) (t Z : ℝ) (hZ : 1 < Z) (hlower : 1 ≤ s.lower)
    (hP : ∀ i, 1 ≤ s.P i) (w : ι → ℝ) (hscale : ∀ i, s.P i = Z ^ w i)
    (hn₁ : frozenCoefficient ch.B₁.val ch.C₁ ch.R₁ s.ν s.W s.P ≠ 0)
    (hn₂ : frozenCoefficient ch.B₂.val ch.E₂ ch.R₂
      ch.first.ν ch.first.W ch.first.P ≠ 0)
    (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val) ⊕ Fin 2))) :
    0 ≤ (∑ i, w i) - (∑ i ∈ ch.indices L a, w i) ∧
      (∑ i, w i) - (∑ i ∈ ch.indices L a, w i) ≤
        Real.logb Z (ch.C₁.absNorm : ℝ) + Real.logb Z (ch.E₂.absNorm : ℝ) +
          Real.logb Z (formalReductionFactor L a (ch.final χ t).P) := by
  have hc := actual_two_common_residual_slot_loss s ch.C₁ ch.R₁ ch.B₁ χ t
    ch.E₂ ch.R₂ ch.B₂ L a Z hZ hlower hP hn₁ hn₂
  have hslot := original_slot_sum s ch χ t Z hZ w hscale L a
  have hs : (∑ i, Real.logb Z (s.P i)) = ∑ i, w i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hscale i, Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  dsimp only at hc
  change 0 ≤ (∑ i, Real.logb Z (s.P i)) - remainingLogs L a Z (ch.final χ t).P ∧
    (∑ i, Real.logb Z (s.P i)) - remainingLogs L a Z (ch.final χ t).P ≤
      Real.logb Z (ch.C₁.absNorm : ℝ) + Real.logb Z (ch.E₂.absNorm : ℝ) +
        Real.logb Z (formalReductionFactor L a (ch.final χ t).P) at hc
  rwa [hs, hslot] at hc

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_common_slot_loss_norm
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_residual_slot_loss
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_two_common_residual_slot_loss
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_original_dictionary_slot_loss
