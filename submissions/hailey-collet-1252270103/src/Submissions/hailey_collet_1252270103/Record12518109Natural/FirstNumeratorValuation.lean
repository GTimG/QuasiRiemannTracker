/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.hailey_collet_1252270103.Cycle61.Moment.CanonicalFirstNorm
import Submissions.hailey_collet_1252270103.Cycle61.Moment.FirstSourceCount
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
Literal first-numerator valuation transport, checked against cached accepted
source modules.  This is a source inequality, not an endpoint theorem.
Arbitrary positive common-prime valuations are allowed; no sixth-free or
equal-support hypothesis is used.
-/

namespace OAI.SevenEighths.Record12518109Natural.FirstNumeratorValuation
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentSecondCanonical
open Cycle61Moment
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
    simp only [ActiveIndex, CenteredMomentActive.activeSupport, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro P _
    by_cases h : netExponent (leftExponent C D P) (rightExponent C D P) = 0
    · simp [sourceExponent, h]
    · simp [sourceExponent, CenteredMomentCanonicalFirst.activeExponent, activePrime, h]
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
    simp only [ActiveIndex, CenteredMomentActive.activeSupport, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro P _
    by_cases h : netExponent (leftExponent C D P) (rightExponent C D P) = 0
    · simp [sourceExponent, h]
    · simp [sourceExponent, CenteredMomentCanonicalFirst.activeExponent, activePrime, h]

end
end OAI.SevenEighths.Record12518109Natural.FirstNumeratorValuation
#print axioms OAI.SevenEighths.Record12518109Natural.FirstNumeratorValuation.numerator_norm_product
