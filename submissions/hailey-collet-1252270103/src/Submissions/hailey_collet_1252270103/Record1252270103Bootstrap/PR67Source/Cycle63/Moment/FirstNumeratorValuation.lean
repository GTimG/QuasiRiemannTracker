import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.CanonicalFirstNorm
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.FirstSourceCount
import Mathlib.Tactic
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Valuation budget of the first source numerator: `4 log N(numerator) ≤ 5 (log N(C) + log N(D))`
for both reflection orientations. From tracker PR #62 (Zhongpai Gao,
`gao-directional-affine-20261016`, `Target836/SourceProvider/ActualValuation.lean`), Apache-2.0.
Released under Apache 2.0. -/
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
    refine Finset.prod_congr rfl fun P _ => ?_
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
    refine Finset.prod_congr rfl fun P _ => ?_
    by_cases h : netExponent (leftExponent C D P) (rightExponent C D P) = 0
    · simp [sourceExponent, h]
    · simp [sourceExponent, h]

end
end OAI.SevenEighths.Cycle63Moment.FirstNumeratorValuation

end Record1252270103Bootstrap.PR67
