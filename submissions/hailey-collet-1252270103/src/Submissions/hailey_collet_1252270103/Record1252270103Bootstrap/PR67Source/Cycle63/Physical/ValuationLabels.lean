import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ValuationCone
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighLedgerGeometry
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The six logarithms of an actual first-source label as a weighted sum of the points of its common
primes, and the balanced common rate at actual labels. From tracker PR #63 (Zhongpai Gao,
`gao-balanced-marked-20261017`, `Target830/Source/{ValuationProducts,Valuation}.lean`), Apache-2.0.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.ValuationCone
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentActive CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSecondCanonical
open Cycle63Moment Cycle63HighGeometry CenteredMomentCommonSupport
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss

theorem active_ideal_product (C D : Ideal O) :
    Ideal.span {activeConductor C D}=
      ∏ P : CommonIndex C D,
        if netExponent (leftExponent C D P) (rightExponent C D P)=0 then 1 else P.val := by
  rw [activeConductor,span_finitePrimeModulus]
  change (∏ P : ActiveIndex C D,P.val.val)=_
  rw [Finset.prod_coe_sort]
  simp only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.prod_filter]
  refine Finset.prod_congr rfl fun P hP => ?_
  split_ifs <;> simp_all

theorem cancelled_ideal_product (left : Bool) (C D : Ideal O) :
    cancelledRadical left C D=
      ∏ P : CommonIndex C D,
        if netExponent (leftExponent C D P) (rightExponent C D P)=
          (if left then 5 else 1) then P.val else 1 := by
  cases left
  · unfold cancelledRadical firstRightCancelledRadical firstRightCancelled
    rw [Finset.prod_filter]
    change (∏ P : ActiveIndex C D,
      (fun Q : CommonIndex C D =>
        if 7-netExponent (leftExponent C D Q) (rightExponent C D Q)=6
        then Q.val else 1) P.val)=_
    rw [Finset.prod_coe_sort (s:=CenteredMomentActive.activeSupport
      (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D))
      (f:=fun Q : CommonIndex C D =>
        if 7-netExponent (leftExponent C D Q) (rightExponent C D Q)=6
        then Q.val else 1)]
    simp only [CenteredMomentActive.activeSupport,Finset.prod_filter]
    refine Finset.prod_congr rfl fun P hP => ?_
    have hk := netExponent_lt_six (leftExponent C D P) (rightExponent C D P)
    split_ifs <;> simp_all; omega
  · unfold cancelledRadical firstLeftCancelledRadical firstLeftCancelled
    rw [Finset.prod_filter]
    change (∏ P : ActiveIndex C D,
      (fun Q : CommonIndex C D =>
        if 1+netExponent (leftExponent C D Q) (rightExponent C D Q)=6
        then Q.val else 1) P.val)=_
    rw [Finset.prod_coe_sort (s:=CenteredMomentActive.activeSupport
      (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D))
      (f:=fun Q : CommonIndex C D =>
        if 1+netExponent (leftExponent C D Q) (rightExponent C D Q)=6
        then Q.val else 1)]
    simp only [CenteredMomentActive.activeSupport,Finset.prod_filter]
    refine Finset.prod_congr rfl fun P hP => ?_
    have hk := netExponent_lt_six (leftExponent C D P) (rightExponent C D P)
    split_ifs <;> simp_all; omega

theorem logb_nat_prod_pow {ι : Type*} [Fintype ι] (N : ι → ℕ) (e : ι → ℕ)
    (hN : ∀ t,0 < N t) (Z : ℝ) :
    Real.logb Z ((∏ t,N t^(e t):ℕ):ℝ)=
      ∑ t,(e t:ℝ)*Real.logb Z (N t:ℝ) := by
  simp only [Nat.cast_prod,Nat.cast_pow]
  rw [Real.logb_prod _ _ (by
    intro t ht
    exact pow_ne_zero _ (by exact_mod_cast (hN t).ne'))]
  simp only [Real.logb_pow]

theorem netExponent_swap_zero (i j : ℕ) :
    netExponent j i=0 ↔ netExponent i j=0 := by unfold netExponent;omega
theorem netExponent_swap_five (i j : ℕ) :
    netExponent j i=5 ↔ netExponent i j=1 := by unfold netExponent;omega
theorem sourceExponent_reflect (i j : ℕ) :
    Cycle63Moment.FirstNumeratorValuation.sourceExponent false i j=
      Cycle63Moment.FirstNumeratorValuation.sourceExponent true j i := by
  have h1 := netExponent_lt_six i j
  have h2 := netExponent_lt_six j i
  have hs : (netExponent i j+netExponent j i)%6=0 := by unfold netExponent;omega
  have hp :
      (netExponent i j=0 ∧ netExponent j i=0) ∨
      (netExponent i j=1 ∧ netExponent j i=5) ∨
      (netExponent i j=2 ∧ netExponent j i=4) ∨
      (netExponent i j=3 ∧ netExponent j i=3) ∨
      (netExponent i j=4 ∧ netExponent j i=2) ∨
      (netExponent i j=5 ∧ netExponent j i=1) := by omega
  rcases hp with hp | hp | hp | hp | hp | hp <;>
    rcases hp with ⟨h,h'⟩ <;> norm_num [Cycle63Moment.FirstNumeratorValuation.sourceExponent,h,h']

def primeWeight (C D : Ideal O) (Z : ℝ) (P : CommonIndex C D) : ℝ :=
  Real.logb Z (P.val.absNorm:ℝ)

theorem common_norm_pos (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    0 < P.val.absNorm :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (commonPrime_supported_ideal C D hC P).1)

theorem primeWeight_nonnegative (C D : Ideal O) (hC : Supported C) (Z : ℝ)
    (hZ : 1 < Z) (P : CommonIndex C D) : 0 ≤ primeWeight C D Z P := by
  apply Real.logb_nonneg hZ
  exact_mod_cast common_norm_pos C D hC P

theorem left_log (C D : Ideal O) (hC : Supported C)
    (heq : primeSupport C=primeSupport D) (Z : ℝ) :
    Real.logb Z (C.absNorm:ℝ)=
      ∑ P : CommonIndex C D,(leftExponent C D P:ℝ)*primeWeight C D Z P := by
  calc
    _ = Real.logb Z ((commonPart C D).absNorm:ℝ) := by
      rw [commonPart_eq_left C D hC.1 heq]
    _ = Real.logb Z ((∏ P : CommonIndex C D,P.val.absNorm^(leftExponent C D P):ℕ):ℝ) := by
      rw [commonPart_left_product,map_prod]
      simp only [map_pow]
    _ = _ := logb_nat_prod_pow _ _ (common_norm_pos C D hC) Z

theorem right_log (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (heq : primeSupport C=primeSupport D) (Z : ℝ) :
    Real.logb Z (D.absNorm:ℝ)=
      ∑ P : CommonIndex C D,(rightExponent C D P:ℝ)*primeWeight C D Z P := by
  calc
    _ = Real.logb Z ((commonPart D C).absNorm:ℝ) := by
      rw [commonPart_eq_left D C hD.1 heq.symm]
    _ = Real.logb Z ((∏ P : CommonIndex C D,P.val.absNorm^(rightExponent C D P):ℕ):ℝ) := by
      rw [commonPart_right_product,map_prod]
      simp only [map_pow]
    _ = _ := logb_nat_prod_pow _ _ (common_norm_pos C D hC) Z

theorem radical_log (C D : Ideal O) (hC : Supported C) (Z : ℝ) :
    Real.logb Z ((commonRadical C D).absNorm:ℝ)=
      ∑ P : CommonIndex C D,primeWeight C D Z P := by
  rw [first_common_radical_product,map_prod]
  simpa [primeWeight] using logb_nat_prod_pow (fun P : CommonIndex C D => P.val.absNorm)
    (fun _ => 1) (common_norm_pos C D hC) Z

theorem active_log (C D : Ideal O) (hC : Supported C) (Z : ℝ) :
    Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      ∑ P : CommonIndex C D,
        (if netExponent (leftExponent C D P) (rightExponent C D P)=0 then (0:ℝ) else 1)*
          primeWeight C D Z P := by
  have hn : (Ideal.span {activeConductor C D}).absNorm=
      ∏ P : CommonIndex C D,P.val.absNorm^
        (if netExponent (leftExponent C D P) (rightExponent C D P)=0 then 0 else 1) := by
    rw [active_ideal_product,map_prod]
    refine Finset.prod_congr rfl fun P hP => ?_
    split_ifs <;> simp_all
  rw [hn]
  simpa only [Nat.cast_ite,Nat.cast_zero,Nat.cast_one,primeWeight] using logb_nat_prod_pow
    (fun P : CommonIndex C D => P.val.absNorm)
    (fun P => if netExponent (leftExponent C D P) (rightExponent C D P)=0 then 0 else 1)
    (common_norm_pos C D hC) Z

theorem numerator_log (left : Bool) (C D : Ideal O) (hC : Supported C) (Z : ℝ) :
    Real.logb Z ((Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm:ℝ)=
      ∑ P : CommonIndex C D,
        (Cycle63Moment.FirstNumeratorValuation.sourceExponent left (leftExponent C D P)
          (rightExponent C D P):ℝ)*primeWeight C D Z P := by
  rw [Cycle63Moment.FirstNumeratorValuation.numerator_norm_product left C D hC]
  exact logb_nat_prod_pow _ _ (common_norm_pos C D hC) Z

theorem cancelled_log (left : Bool) (C D : Ideal O) (hC : Supported C) (Z : ℝ) :
    Real.logb Z ((cancelledRadical left C D).absNorm:ℝ)=
      ∑ P : CommonIndex C D,
        (if netExponent (leftExponent C D P) (rightExponent C D P)=
          (if left then 5 else 1) then (1:ℝ) else 0)*primeWeight C D Z P := by
  have hn : (cancelledRadical left C D).absNorm=
      ∏ P : CommonIndex C D,P.val.absNorm^
        (if netExponent (leftExponent C D P) (rightExponent C D P)=
          (if left then 5 else 1) then 1 else 0) := by
    rw [cancelled_ideal_product,map_prod]
    refine Finset.prod_congr rfl fun P hP => ?_
    split_ifs <;> simp_all
  rw [hn]
  simpa only [Nat.cast_ite,Nat.cast_zero,Nat.cast_one,primeWeight] using logb_nat_prod_pow
    (fun P : CommonIndex C D => P.val.absNorm)
    (fun P => if netExponent (leftExponent C D P) (rightExponent C D P)=
      (if left then 5 else 1) then 1 else 0) (common_norm_pos C D hC) Z

def actualVector (reflected : Bool) (C D : Ideal O) (Z : ℝ) : Fin 6 → ℝ :=
  ![Real.logb Z ((if reflected then D else C).absNorm:ℝ),
    Real.logb Z ((if reflected then C else D).absNorm:ℝ),
    Real.logb Z ((commonRadical C D).absNorm:ℝ),
    Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ),
    Real.logb Z ((Ideal.span
      {if !reflected then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm:ℝ),
    Real.logb Z ((cancelledRadical (!reflected) C D).absNorm:ℝ)]

/-- Exact actual cone membership. The two original ideals have equal prime
support, so their full norms are exhausted by the positive common valuations. -/
theorem actualVector_eq_weighted (reflected : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C=primeSupport D) (Z : ℝ) :
    actualVector reflected C D Z=
      weighted Finset.univ
        (if reflected then rightExponent C D else leftExponent C D)
        (if reflected then leftExponent C D else rightExponent C D)
        (primeWeight C D Z) := by
  cases reflected
  · funext k
    fin_cases k
    · simpa [actualVector,weighted,point,mul_comm] using left_log C D hC heq Z
    · simpa [actualVector,weighted,point,mul_comm] using right_log C D hC hD heq Z
    · simpa [actualVector,weighted,point,mul_comm] using radical_log C D hC Z
    · simpa [actualVector,weighted,point,mul_comm] using active_log C D hC Z
    · simpa [actualVector,weighted,point,mul_comm] using numerator_log true C D hC Z
    · simpa [actualVector,weighted,point,mul_comm] using cancelled_log true C D hC Z
  · funext k
    fin_cases k
    · simpa [actualVector,weighted,point,mul_comm] using right_log C D hC hD heq Z
    · simpa [actualVector,weighted,point,mul_comm] using left_log C D hC heq Z
    · simpa [actualVector,weighted,point,mul_comm] using radical_log C D hC Z
    · simpa [actualVector,weighted,point,netExponent_swap_zero,mul_comm] using active_log C D hC Z
    · have hh := numerator_log false C D hC Z
      simp only [sourceExponent_reflect] at hh
      simpa [actualVector,weighted,point,mul_comm] using hh
    · have hh := cancelled_log false C D hC Z
      simpa [actualVector,weighted,point,netExponent_swap_five,mul_comm] using hh

theorem actual_first_common_saving (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z rho delta : ℝ) (hZ : 1 < Z) (hr : 1/4 ≤ rho) (hrhi : rho ≤ 23/50) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ)
    let R0 := Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ)
    firstCommon rho delta c d R E Lc R0-surplus c d p R ≤
      -(delta-max (3/19) (4*rho-5/4))*c-E := by
  have hv := actualVector_eq_weighted reflected l.1.1 l.1.2 hC hD heq Z
  have hw := fun P (_hP : P ∈ (Finset.univ : Finset (CommonIndex l.1.1 l.1.2))) =>
    primeWeight_nonnegative l.1.1 l.1.2 hC Z hZ P
  have hi : ∀ P ∈ (Finset.univ : Finset (CommonIndex l.1.1 l.1.2)),
      0 < (if reflected then rightExponent l.1.1 l.1.2 else leftExponent l.1.1 l.1.2) P := by
    intro P hP
    cases reflected
    · exact leftExponent_pos _ _ P
    · exact rightExponent_pos _ _ P
  have hj : ∀ P ∈ (Finset.univ : Finset (CommonIndex l.1.1 l.1.2)),
      0 < (if reflected then leftExponent l.1.1 l.1.2 else rightExponent l.1.1 l.1.2) P := by
    intro P hP
    cases reflected
    · exact rightExponent_pos _ _ P
    · exact leftExponent_pos _ _ P
  have hh := common_weighted_saving Finset.univ _ _ _ hw hi hj rho delta
    (Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)) hr hrhi
  dsimp only at hh
  rw [←hv] at hh
  simpa [actualVector,firstSourceNumerator] using hh

end

end OAI.SevenEighths.Cycle63Moment.ValuationCone

end Record1252270103Bootstrap.PR67
