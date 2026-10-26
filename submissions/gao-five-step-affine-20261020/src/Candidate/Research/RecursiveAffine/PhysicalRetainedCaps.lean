/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0.
The common reduction proof follows the exact PR67 FinalCapacity.Allocation
proof; its unused Candidate imports are omitted. -/
import Candidate.Research.RecursiveAffine.RetainedFTwoStage
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI.SevenEighths.Cycle153PhysicalCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The norm of the actual common ideal is paid by its actual raw reduction,
with a fixed support cost. No size of a residual ideal family occurs. -/
theorem actual_common_reduction_lower (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (C R : Ideal O) (B : actualAllocations s.pools C)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (C.absNorm : ℝ) - (N : ℝ) * Real.logb Z b ≤
      Real.logb Z (rawReduction B.val s.P) := by
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hc := norm_ge_one C (allocation_ne s C B)
  have hn := (actual_reduction_norm B.val (alloc_ne s C B) C R
    (allocation_product s C B) s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx => ⟨(s.slot_support i hx).1, ((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn' : (C.absNorm : ℝ) ≤ b ^ N * rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  have hh := Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le hc) hn'
  rw [Real.logb_mul (pow_pos (zero_lt_one.trans_le hb) _).ne' hr.ne', Real.logb_pow] at hh
  linarith

/-- Any literal affine upper plane and its cell bound pay the original
weighted capacity. This is independent of the old fixed ledger constants. -/
theorem original_affine_cell_capacity (s : Input ι)
    (Z κ unit lam B b : ℝ) (hZ : 1 < Z) (hlam : lam ≤ 6 * κ)
    (hslot : (∑ i, Real.logb Z (s.P i)) ≤ b * unit)
    (hplane : length Z s.X₁ + length Z s.X₂ +
      lam * (∑ i, Real.logb Z (s.P i)) ≤ B * unit) :
    Real.logb Z (preVolume s.toData) +
        (6 * κ - 1) * (∑ i, Real.logb Z (s.P i)) - unit ≤
      unit * (B - 1 + (6 * κ - lam) * b) := by
  have hm := mul_le_mul_of_nonneg_left hslot (sub_nonneg.mpr hlam)
  have h₁ := raw_log_le_length Z s.X₁ hZ s.X₁_pos
  have h₂ := raw_log_le_length Z s.X₂ hZ s.X₂_pos
  change Real.logb Z (volume s) + _ - _ ≤ _
  rw [input_volume_log]
  nlinarith only [hm, h₁, h₂, hplane]

variable (s : Input ι) (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
variable (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
variable (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
variable (χ : Character) (t : ℝ) (C₂ R₂ : Ideal O)
variable (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
variable (hn₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P ≠ 0)
variable (hn₂ : frozenCoefficient B₂.val C₂ R₂
  (child s C₁ R₁ B₁ χ t).ν (child s C₁ R₁ B₁ χ t).W
  (child s C₁ R₁ B₁ χ t).P ≠ 0)
variable (L : Ideal O)
variable (a : Allocation L (Finset.univ : Finset
  ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2)))
variable (Z κ nominal : ℝ) (hZ : 1 < Z) (hκ : (1 / 6 : ℝ) ≤ κ)
variable (hP : ∀ i, 1 ≤ s.P i)
variable (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
variable (hprod : X₁ * X₂ = (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₁ *
  (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂).X₂)
variable (z : O) (hne : let v := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
  allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P L a
    v.W₁ v.W₂ X₁ X₂ ≠ 0)

include hb hcard hs hn₁ hn₂ hZ hκ hP hX₁ hX₂ hprod hne

/-- Both actual common ideal norms and the residual reduction survive in
the same supported-source inequality, with only the fixed support padding. -/
theorem two_stage_common_norm_capacity :
    let final := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
    plainLogs L a Z X₁ X₂ + 6 * κ * remainingLogs L a Z final.P - nominal ≤
      Real.logb Z (preVolume s.toData) - Real.logb Z (C₁.absNorm : ℝ) -
        Real.logb Z (C₂.absNorm : ℝ) -
        Real.logb Z (formalReductionFactor L a final.P) - nominal +
        (6 * κ - 1) * (∑ i, Real.logb Z (s.P i)) +
        (2 * (N : ℝ) * Real.logb Z b + Real.logb Z (max 1 s.b₁ * max 1 s.b₂)) := by
  have hc := Cycle152RetainedFReturn.two_stage_affine_capacity_retained_F
    s C₁ R₁ B₁ χ t C₂ R₂ B₂ L a Z κ nominal hZ hκ hP
    X₁ X₂ hX₁ hX₂ hprod z hne
  have hr₁ := actual_common_reduction_lower N b hb s hcard hs C₁ R₁ B₁ hn₁ Z hZ
  have hcard₁ : Fintype.card (CenteredMomentCommonProfile.liveIndices B₁.val) ≤ N :=
    (live_card_le B₁.val).trans hcard
  have hr₂ := actual_common_reduction_lower N b hb
    (child s C₁ R₁ B₁ χ t) hcard₁ hs C₂ R₂ B₂ hn₂ Z hZ
  dsimp only at hc ⊢
  linarith only [hc, hr₁, hr₂]

/-- The two source caps used by a real LOW child. The affine cap is the
literal input-region hypothesis; the whole returned-energy theorem is not
assumed. The same residual F appears in BOTH resulting caps. -/
theorem two_stage_low_source_caps (unit amp omega shift otherLog gap : ℝ)
    (hnominal : nominal = unit -
      max (Real.logb Z (C₁.absNorm : ℝ) - otherLog) 0 - 6 * amp - omega - shift)
    (hparent : Real.logb Z (preVolume s.toData) +
      (6 * κ - 1) * (∑ i, Real.logb Z (s.P i)) - unit ≤ gap) :
    let final := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
    let F := Real.logb Z (formalReductionFactor L a final.P)
    let pad := 2 * (N : ℝ) * Real.logb Z b + Real.logb Z (max 1 s.b₁ * max 1 s.b₂)
    (plainLogs L a Z X₁ X₂ + remainingLogs L a Z final.P ≤
      Real.logb Z (preVolume s.toData) - Real.logb Z (C₁.absNorm : ℝ) -
        Real.logb Z (C₂.absNorm : ℝ) - F + pad) ∧
    (plainLogs L a Z X₁ X₂ + 6 * κ * remainingLogs L a Z final.P - nominal ≤
      gap + 6 * amp + omega + pad -
        (min (Real.logb Z (C₁.absNorm : ℝ)) otherLog +
          (Real.logb Z (C₂.absNorm : ℝ) - shift)) - F) := by
  have hc := two_stage_common_norm_capacity s N b hb hcard hs C₁ R₁ B₁ χ t C₂ R₂ B₂ hn₁ hn₂
    L a Z κ nominal hZ hκ hP X₁ X₂ hX₁ hX₂ hprod z hne
  have ht := two_stage_common_norm_capacity s N b hb hcard hs C₁ R₁ B₁ χ t C₂ R₂ B₂ hn₁ hn₂
    L a Z (1 / 6) 0 hZ le_rfl hP X₁ X₂ hX₁ hX₂ hprod z hne
  have hmm : min (Real.logb Z (C₁.absNorm : ℝ)) otherLog +
      max (Real.logb Z (C₁.absNorm : ℝ) - otherLog) 0 = Real.logb Z (C₁.absNorm : ℝ) := by
    rcases le_total (Real.logb Z (C₁.absNorm : ℝ)) otherLog with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  dsimp only at hc ht ⊢
  constructor
  · norm_num at ht
    exact ht
  · linarith only [hc, hparent, hnominal, hmm]

end
end OAI.SevenEighths.Cycle153PhysicalCapacity

#print axioms OAI.SevenEighths.Cycle153PhysicalCapacity.original_affine_cell_capacity
#print axioms OAI.SevenEighths.Cycle153PhysicalCapacity.two_stage_low_source_caps
