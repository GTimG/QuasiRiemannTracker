/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.ValuationProducts
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace OAI.SevenEighths.Record12518109Natural.Valuation
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentActive CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSecondCanonical
open Cycle61Moment Cycle61HighGeometry CenteredMomentCommonSupport
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss
local notation "O" => HeckeFamily.O

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
    apply Finset.prod_congr rfl
    intro P hP
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
        (Record12518109Natural.FirstNumeratorValuation.sourceExponent left (leftExponent C D P)
          (rightExponent C D P):ℝ)*primeWeight C D Z P := by
  rw [Record12518109Natural.FirstNumeratorValuation.numerator_norm_product left C D hC]
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
    apply Finset.prod_congr rfl
    intro P hP
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

/-- The actual HIGH input in the physical orientation. It uses the complete
supported ideal pair and supplies the common inequality without a scalar
valuation hypothesis. The inactive-projector loss is only discarded here. -/
theorem actual_first_common_gamma (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z delta : ℝ) (hZ : 1 < Z) (hd : 31/50 ≤ delta) (hdhi : delta ≤ 3/4) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ)
    let R0 := Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ)
    firstCommon (LocalMoment.unmarkedDensity delta) delta c d R E Lc R0-
      surplus c d p R ≤ -commonGamma delta*c := by
  have hr := rho_extended_range (show (405/662:ℝ) ≤ delta by linarith) hdhi
  have hh := actual_first_common_saving reflected l hC hD heq Z (rho delta) delta hZ hr.1 hr.2
  obtain ⟨_,hE,_,_,_,_,_⟩ := actual_first_gates (!reflected) l hC hD Z hZ
  dsimp only at hh hE ⊢
  unfold commonGamma
  rw [rho_eq_local] at hh ⊢
  linarith only [hh,hE]

end
end OAI.SevenEighths.Record12518109Natural.Valuation
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.actualVector_eq_weighted
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.actual_first_common_saving
#print axioms OAI.SevenEighths.Record12518109Natural.Valuation.actual_first_common_gamma
