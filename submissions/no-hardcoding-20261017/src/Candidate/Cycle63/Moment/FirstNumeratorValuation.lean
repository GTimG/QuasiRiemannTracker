/- Valuation budget of the first source numerator: `4 log N(numerator) ≤ 5 (log N(C) + log N(D))`
for both reflection orientations. From tracker PR #62 (Zhongpai Gao,
`gao-directional-affine-20261016`, `Target836/SourceProvider/ActualValuation.lean`), Apache-2.0.
Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.CanonicalFirstNorm
import Candidate.Cycle63.Moment.FirstSourceCount
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
The exponent of a common prime in the first source numerator is at most `5/4` of the sum of its
exponents in `C` and `D`; arbitrary positive common-prime valuations are allowed.
-/

namespace OAI.SevenEighths.Cycle63Moment.FirstNumeratorValuation
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentSecondCanonical
open Cycle63Moment
local notation "O" => HeckeFamily.O

def sourceExponent (left : Bool) (i j : ℕ) : ℕ :=
  if netExponent i j = 0 then 0 else
    if left then
      if 1+netExponent i j = 6 then 0 else 1+netExponent i j
    else
      if 7-netExponent i j = 6 then 0 else 7-netExponent i j

theorem sourceExponent_budget (left : Bool) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    4*sourceExponent left i j ≤ 5*(i+j) := by
  have hk := netExponent_lt_six i j
  have he : sourceExponent left i j ≤ 5 := by
    cases left <;> unfold sourceExponent <;> split_ifs <;> omega
  by_cases hs : 4 ≤ i+j
  · omega
  · have hi2 : i ≤ 2 := by omega
    have hj2 : j ≤ 2 := by omega
    interval_cases i <;> interval_cases j <;> cases left <;>
      norm_num [sourceExponent, netExponent] at *

theorem numerator_norm_product (left : Bool) (C D : Ideal O) (hC : Supported C) :
    (Ideal.span {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm =
      ∏ P : CommonIndex C D,
        P.val.absNorm ^ sourceExponent left (leftExponent C D P) (rightExponent C D P) := by
  cases left
  · rw [show (if false then firstLeftUncancelled C D else firstRightUncancelled C D) =
        firstRightUncancelled C D by rfl]
    rw [firstRightUncancelled, powered_numerator_norm]
    simp_rw [firstSignedPrime_span C D hC]
    rw [Finset.prod_filter]
    change (∏ P : ActiveIndex C D,
      if 7-activeExponent C D P ≠ 6 then (activePrime C D P).absNorm^(7-activeExponent C D P)
      else 1) = _
    change (∏ P : ActiveIndex C D,
      (fun Q : CommonIndex C D =>
        if 7-netExponent (leftExponent C D Q) (rightExponent C D Q) ≠ 6 then
          Q.val.absNorm^(7-netExponent (leftExponent C D Q) (rightExponent C D Q))
        else 1) P.val) = _
    rw [Finset.prod_coe_sort
      (s := CenteredMomentActive.activeSupport (Finset.univ : Finset (CommonIndex C D))
        (leftExponent C D) (rightExponent C D))
      (f := fun Q : CommonIndex C D =>
        if 7-netExponent (leftExponent C D Q) (rightExponent C D Q) ≠ 6 then
          Q.val.absNorm^(7-netExponent (leftExponent C D Q) (rightExponent C D Q))
        else 1)]
    simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro P _
    by_cases h : netExponent (leftExponent C D P) (rightExponent C D P) = 0
    · simp [sourceExponent, h]
    · simp [sourceExponent, h]
  · rw [show (if true then firstLeftUncancelled C D else firstRightUncancelled C D) =
        firstLeftUncancelled C D by rfl]
    rw [firstLeftUncancelled, powered_numerator_norm]
    simp_rw [firstSignedPrime_span C D hC]
    rw [Finset.prod_filter]
    change (∏ P : ActiveIndex C D,
      if 1+activeExponent C D P ≠ 6 then (activePrime C D P).absNorm^(1+activeExponent C D P)
      else 1) = _
    change (∏ P : ActiveIndex C D,
      (fun Q : CommonIndex C D =>
        if 1+netExponent (leftExponent C D Q) (rightExponent C D Q) ≠ 6 then
          Q.val.absNorm^(1+netExponent (leftExponent C D Q) (rightExponent C D Q))
        else 1) P.val) = _
    rw [Finset.prod_coe_sort
      (s := CenteredMomentActive.activeSupport (Finset.univ : Finset (CommonIndex C D))
        (leftExponent C D) (rightExponent C D))
      (f := fun Q : CommonIndex C D =>
        if 1+netExponent (leftExponent C D Q) (rightExponent C D Q) ≠ 6 then
          Q.val.absNorm^(1+netExponent (leftExponent C D Q) (rightExponent C D Q))
        else 1)]
    simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro P _
    by_cases h : netExponent (leftExponent C D P) (rightExponent C D P) = 0
    · simp [sourceExponent, h]
    · simp [sourceExponent, h]

theorem literal_numerator_norm_bound (left : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : D ≠ 0) :
    (Ideal.span {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm^4 ≤
      (C.absNorm*D.absNorm)^5 := by
  have hcommon :
      (Ideal.span {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm^4 ≤
        ((commonPart C D).absNorm*(commonPart D C).absNorm)^5 := by
    rw [numerator_norm_product left C D hC, ← Finset.prod_pow]
    have hprod : ((commonPart C D).absNorm*(commonPart D C).absNorm)^5 =
        ∏ P : CommonIndex C D,
          P.val.absNorm^(5*(leftExponent C D P+rightExponent C D P)) := by
      rw [commonPart_left_product, commonPart_right_product, map_prod, map_prod,
        ← Finset.prod_mul_distrib, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro P _
      rw [map_pow, map_pow, ← pow_add, ← pow_mul]
      congr 1
      omega
    rw [hprod]
    apply Finset.prod_le_prod
    intro P _
    rw [← pow_mul]
    apply pow_le_pow_right'
      (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (commonPrime_supported_ideal C D hC P).1))
    simpa only [Nat.mul_comm] using sourceExponent_budget left
      (leftExponent C D P) (rightExponent C D P)
      (leftExponent_pos C D P) (rightExponent_pos C D P)
  exact hcommon.trans (Nat.pow_le_pow_left
    (Nat.mul_le_mul (absNorm_commonPart_le C D hC.1) (absNorm_commonPart_le D C hD)) 5)

theorem literal_numerator_log_bound (left : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : D ≠ 0) (Z : ℝ) (hZ : 1<Z) :
    4*Real.logb Z ((Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm:ℝ) ≤
      5*(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)) := by
  have hnum : 0 < (Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm := by
    cases left <;>
      exact powered_numerator_norm_pos _ _ _ (fun P _ => firstSignedPrime_supported C D hC P)
  have hn := Real.logb_le_logb_of_le hZ
    (show (0:ℝ) < ((Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm:ℝ)^4 by
      positivity)
    (show ((Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm:ℝ)^4 ≤
      ((C.absNorm:ℝ)*D.absNorm)^5 by exact_mod_cast literal_numerator_norm_bound left C D hC hD)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_mul
    (by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
    (by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hD)] at hn
  simpa only [Nat.cast_ofNat] using hn

/-- The requested source-label statement, independent of the inactive subset. -/
theorem actual_firstSourceNumerator_log_bound (left : Bool) (label : FirstSourceLabel)
    (hC : Supported label.1.1) (hD : label.1.2 ≠ 0) (Z : ℝ) (hZ : 1<Z) :
    4*Real.logb Z ((Ideal.span {firstSourceNumerator left label}).absNorm:ℝ) ≤
      5*(Real.logb Z (label.1.1.absNorm:ℝ)+Real.logb Z (label.1.2.absNorm:ℝ)) := by
  exact literal_numerator_log_bound left label.1.1 label.1.2 hC hD Z hZ

end
end OAI.SevenEighths.Cycle63Moment.FirstNumeratorValuation
