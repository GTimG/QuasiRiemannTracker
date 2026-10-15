/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B082
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalLow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSourceDiagonal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder

/- BEGIN ORIGINAL Cycle61.Physical.ExceptionalReference; sha256 c93425aa96193da8a966382b373c1d9dee1cb1120089f32f5f00e504ba07a8c4 -/
section
                                      
                                                                   
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle61ExceptionalReference
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedAllowance
open CenteredMomentDescentLedger CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentFirstScale ConcreteTraceCRT
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O"=>HeckeFamily.O

open CenteredMomentFirstMixedNormalizationActual CenteredMomentCommonRadiusSaving
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCompleteCommon
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius
theorem actual_side_exceptional_reference (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z j g w wo ell Bside:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let q:=Real.logb Z (τ.modulus.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    let M:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost;
    (V/(C.absNorm:ℝ))*Z^(-wo)*(V/(C.absNorm:ℝ)/Z^w)^((1:ℝ)/3)*
      (Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^Bside)=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo Bside g ell):=by
  have hh:=exceptional_reference_identity Z V (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)
    ((Ideal.span {activeConductor C D}).absNorm:ℝ) K (τ.modulus.absNorm:ℝ)
    w wo Bside j g ell hZ hV (norm_pos C hC.1) (norm_pos D hD.1)
    (norm_pos _ (subsetGenerator_supported C D hC E).1) (active_norm_pos C D) hK
    (norm_pos _ τ.modulus_ne_bot)
  dsimp only at hh ⊢
  rw [actual_reference_width η τ C D hC E K Z hK hZ hmod] at hh
  rw [nominal_equal_support C D _ hC.1 hD.1 hCD K V]
  exact hh

theorem actual_main_side_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r plainLoss : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0< K)(hX:0< X)
    (hrange : (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-
      Real.logb Z (I.absNorm:ℝ)-plainLoss≤ r) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+4*sigma/3+5*(delta+reserve)/6+2*plainLoss/3):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=Cycle61.Physical.actual_main_side_saving η τ fixedBadMask I J E hI hJ A
    K X Z j (sigma/3) delta reserve hZ hmod
  have hsigma : 3*(sigma/3)=sigma := by ring
  simp only [hsigma] at hs
  simp only [hc,hd] at hs
  have he:=(actual_side_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) (max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0< mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith [le_max_left r 0]

theorem actual_error_side_reference_le (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z j g Bside:ℝ)(hK:0< K)(hV:0< V)(hZ:1< Z)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let q:=Real.logb Z (τ.modulus.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V);
    let M:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost;
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*
      (V/(C.absNorm:ℝ)/(normValue p)^k)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^Bside)≤
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) (errorRemoval p Z k) q
        (errorMoving p Z k) Bside g 0):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hCpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hnpos:=normValue_pos p hp
  have hh:=actual_side_exceptional_reference η τ C D hC hD hCD E K V Z j g
    (errorRemoval p Z k) (errorMoving p Z k) 0 Bside hK hV hZ hmod
  dsimp only at hh ⊢
  rw [errorRemoval_power p hp Z hZ k,neg_zero,Real.rpow_zero,mul_one] at hh
  rw [←hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (actual_error_weight p hp Z hZ k hk) (by positivity)

theorem actual_error_side_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (max (3*c-5*d-R) 0/6)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  have hactive := canonical_active_log_le η τ m I J A Z hZ hmod
  have hmax := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower
    (Real.logb Z ((commonPart I J).absNorm:ℝ))
    (Real.logb Z ((commonPart J I).absNorm:ℝ))
    (nominalLog I J E K X Z-j) (Real.logb Z (τ.modulus.absNorm:ℝ))
    (max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6) sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq (by positivity) (by linarith [hactive.2]) hl hu k hk using 1
  congr 1
  ring

theorem actual_error_side_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r plainLoss : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0< K)(hX:0< X)
    (hrange : (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-
      Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k-plainLoss≤ r) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+3*sigma/2+5*(delta+reserve)/6+2*plainLoss/3):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_side_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hs
  simp only [hc,hd] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hl : 0 ≤ Real.logb Z (normValue p0) :=
    Real.logb_nonneg hZ (normValue_ge_one p0 hp.1.ne_zero)
  have hw : 0 ≤ errorRemoval p0 Z k := by unfold errorRemoval; positivity
  have he:=actual_error_side_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) (max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0< errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith [le_max_left r 0]

end SevenEighths.Cycle61ExceptionalReference
end
end OAI
#print axioms OAI.SevenEighths.Cycle61ExceptionalReference.actual_main_side_exceptional_reference

#print axioms OAI.SevenEighths.Cycle61ExceptionalReference.actual_error_side_exceptional_reference

end
/- END ORIGINAL Cycle61.Physical.ExceptionalReference -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalRadius; sha256 cffd84d250f9896df18f5274b325bdaf4609ab74dc02c0a3833c60b5523fc732 -/
section
                                            
                                                              
                                                                       

namespace OAI.SevenEighths.Cycle61FinalRadius
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondHeightFamily CenteredMomentFirstMixedRoot CenteredMomentFirstPhysicalSource
open CenteredMomentSecondRetainedWidth CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn

/-- This declared second Fourier radius dominates the genuine first common
child's squared volume divided by its physical radius. -/
theorem actual_second_radius_admissible {ι : Type*} [Fintype ι]
    (N : ℕ) (b : ℝ) (hb : 1≤ b) (s : Input ι)
    (hcard : Fintype.card ι≤ N) (hs : s.upper≤ b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t K : ℝ)
    (hK : 0< K) (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    (volume (child s C R B τ t))^2/K≤(b^N*volume s/(C.absNorm:ℝ))^2/K := by
  have hh := common_volume_le N b hb s hcard hs C R B τ t hne
  apply div_le_div_of_nonneg_right _ hK.le
  exact pow_le_pow_left₀ (volume_pos _).le hh 2

/-- The same completed cutoff supplies an actual ball majorant for every
retained row, with no new arithmetic puncture. -/
theorem actual_retained_majorant (R : ℝ) (G V z : O)
    (h : retainedWeight R (normValue ((G*V)*z))≠0) :
    1≤(ballProfile (normValue z/(max 1 (4*R/(normValue G*normValue V))))).re := by
  obtain ⟨_,_,_,_,hz,hu,_⟩ := retained_geometry R G V z h
  have hH : 0< max 1 (4*R/(normValue G*normValue V)) :=
    zero_lt_one.trans_le (le_max_left _ _)
  rw [ballProfile_one _ (div_nonneg (by linarith) hH.le)
    ((div_le_one hH).mpr (hu.trans (le_max_right _ _)))]
  norm_num

/-- All support and fixed-presentation losses are paid by one threshold
chosen before the moving characters, common parts, and retained rows. -/
theorem fixed_radius_loss_eventually (N : ℕ) (b ε : ℝ) (hb : 0< b) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1< Z ∧
      Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+
        Real.logb Z (4*(fixedFactor:ℝ))≤ε := by
  have hf := fixedPresentationCost_pos
  have hg : 0<(fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  let A := fixedPresentationCost*b^(2*N)*(4*(fixedFactor:ℝ))
  have hA : 0< A := by dsimp [A]; positivity
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) A,
    Filter.eventually_gt_atTop (1:ℝ)] with Z hAZ hZ
  refine ⟨hZ,?_⟩
  have hh := Real.logb_le_logb_of_le hZ hA hAZ
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  dsimp [A] at hh
  simp (disch := positivity) only [Real.logb_mul, Real.logb_pow] at hh
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh
  simpa only [Real.logb_mul (by norm_num : (4:ℝ)≠0) hg.ne'] using hh

/-- The second Fourier cutoff uses an upper bound for the actual first-child
volume. Its logarithm keeps the six-amplifier gain from the real main ball. -/
theorem main_inverse_radius_log (η τ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0< K) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kmain := mainCommonRadius Z d K0 c (3*a) δ reserve
    Real.logb Z (frequencyRadius ((b^N*V/(C.absNorm:ℝ))^2/Kmain) Z ξ)+
      Real.logb Z (τ.modulus.absNorm:ℝ) =
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-d) 0-6*a-δ-reserve+
        Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2 := by
  dsimp only
  have hc := norm_pos C hC.1
  have hd := norm_pos D hD.1
  have hE := norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR := active_norm_pos C D
  have hz : 0< Z := zero_lt_one.trans hZ
  have hwidth := actual_reference_width η τ C D hC E K Z hK hZ hmod
  unfold frequencyRadius mainCommonRadius nominalLog
  rw [nominal_equal_support C D _ hC.1 hD.1 heq K V]
  simp (disch := positivity) only [Real.logb_mul, Real.logb_div, Real.logb_pow,
    Real.logb_rpow hz hZ.ne']
  by_cases h : Real.logb Z (C.absNorm:ℝ) ≤ Real.logb Z (D.absNorm:ℝ)
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    linarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    linarith

/-- The physical second row cutoff and its actual natural conductor cancel
the nonunit radical. Nonempty support justifies completing the scale at one. -/
theorem actual_main_final_width (η τ χ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0< K) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (G V₂ z : O) (U : Ideal O) (hU : U≠0)
    (hN : χ.modulus.absNorm≤τ.modulus.absNorm*fixedFactor*U.absNorm*(Ideal.span {V₂}).absNorm) :
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kmain := mainCommonRadius Z d K0 c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/(C.absNorm:ℝ))^2/Kmain) Z ξ
    retainedWeight R (normValue ((G*V₂)*z))≠0 →
      Real.logb Z (max 1 (4*R/(normValue G*normValue V₂)))+
        Real.logb Z (χ.modulus.absNorm:ℝ) ≤
      (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-d) 0-6*a-δ-reserve-
        Real.logb Z (normValue G)+Real.logb Z (U.absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hrow
  have hh := retained_log_budget τ χ G V₂ z U hU hN _ Z hZ hrow
  have he := main_inverse_radius_log η τ C D hC hD heq E K V Z a δ reserve ξ b N
    hK hV hZ hb hmod
  dsimp only at he
  linarith

end
end OAI.SevenEighths.Cycle61FinalRadius
#print axioms OAI.SevenEighths.Cycle61FinalRadius.main_inverse_radius_log
#print axioms OAI.SevenEighths.Cycle61FinalRadius.actual_main_final_width

#print axioms OAI.SevenEighths.Cycle61FinalRadius.actual_second_radius_admissible
#print axioms OAI.SevenEighths.Cycle61FinalRadius.actual_retained_majorant
#print axioms OAI.SevenEighths.Cycle61FinalRadius.fixed_radius_loss_eventually

end
/- END ORIGINAL Cycle61.Physical.FinalRadius -/

/- BEGIN ORIGINAL Cycle61.Physical.NominalRadius; sha256 e3d1c26a1c08928519f6675bb02293f255e25a5b04e42c17d2cc2d1dddba562d -/
section
                                   

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61NominalRadius
noncomputable section
open scoped Classical
open HeckeFamily ActualEisensteinCubic CenteredMomentFirstScale CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- The nominal radius is computed from the actual common labels, active
radical, subset radical, original volume, and original radial scale. -/
theorem actual_nominal_log (C D E : Ideal O) (hC : C≠0) (hD : D≠0)
    (hE : E≠0) (heq : primeSupport C=primeSupport D) (K V Z : ℝ)
    (hK : 0< K) (hV : 0< V) (_hZ : 1< Z) :
    nominalLog C D E K V Z = 2*Real.logb Z V-Real.logb Z (C.absNorm:ℝ)-
      Real.logb Z (D.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+
      Real.logb Z (E.absNorm:ℝ)-Real.logb Z K := by
  have hc := norm_pos C hC
  have hd := norm_pos D hD
  have he := norm_pos E hE
  have hr := active_norm_pos C D
  unfold nominalLog
  rw [nominal_equal_support C D E hC hD heq K V]
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow]
  ring

/-- Specializing the original radial scale to Z^M removes the nominal-radius
gate in the second-zero estimate; only the actual original volume cap remains. -/
theorem actual_nominal_le (C D E : Ideal O) (hC : C≠0) (hD : D≠0)
    (hE : E≠0) (heq : primeSupport C=primeSupport D) (V Z M A : ℝ)
    (hV : 0< V) (hZ : 1< Z) (hvol : V≤ Z^A) :
    nominalLog C D E (Z^M) V Z ≤ 2*A-Real.logb Z (C.absNorm:ℝ)-
      Real.logb Z (D.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+
      Real.logb Z (E.absNorm:ℝ)-M := by
  have hz := zero_lt_one.trans hZ
  rw [actual_nominal_log C D E hC hD hE heq _ _ _ (Real.rpow_pos_of_pos hz _) hV hZ,
    Real.logb_rpow hz hZ.ne']
  have hh := Real.logb_le_logb_of_le hZ hV hvol
  rw [Real.logb_rpow hz hZ.ne'] at hh
  linarith

end
end OAI.SevenEighths.Cycle61NominalRadius
#print axioms OAI.SevenEighths.Cycle61NominalRadius.actual_nominal_log
#print axioms OAI.SevenEighths.Cycle61NominalRadius.actual_nominal_le

end
/- END ORIGINAL Cycle61.Physical.NominalRadius -/

/- BEGIN ORIGINAL Cycle61.Physical.SecondZero.Source; sha256 c784059d756addd906381ee28cf0b469c4957b6d25eb2120fcdae13e2611962a -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                               
                                                                

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle61SecondZero
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceRow
open EisensteinSchwartzPoisson CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O
local instance {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- These are the actual source profile and support factors; independent
plain and slot heights remain in the literal input profiles. -/
def zeroControl {a b : ℝ} (s : Input ι) (p : Profiles a b) (ε : ℝ) : ℝ :=
  (2*p.control {(0,0)}*(∏ i, s.M i))^2 *
    (1+(∏ i, max 0 (s.hi i))*b*b)^(1+ε)

omit [DecidableEq ι] in
lemma zeroControl_nonneg {a b : ℝ} (s : Input ι) (p : Profiles a b) (ε : ℝ) :
    0 ≤ zeroControl s p ε := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by
      have hp := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => le_max_left 0 (s.hi i))
      nlinarith [sq_nonneg b]) _)

lemma singleton_control {a b : ℝ} (p : Profiles a b) :
    p.control {(0,0)} = SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1) := by
  simp [Profiles.control,sourceControl,schwartzSeminormFamily]

/-- Genuine second diagonal, uniformly at every positive physical radius.
The original centered finite-column coefficient and divisor seed are retained. -/
theorem actual_second_zero_radius (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι ≤ N → ∀ (a b : ℝ), 0 < a → 0 ≤ b →
    ∀ (s : Input ι) (p : Profiles a b), s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ), 0 < K →
    ‖((K : ℂ)*paperRadialFourier W 0)*
      sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) s.η s.t‖/volume s.toData ≤
      C*zeroControl s p ε*‖paperRadialFourier W 0‖*K*
        (volume s.toData)^ε/(seed.absNorm : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := CenteredMomentSecondSourceDiagonal.actual_second_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard a b ha hb s p h₁ h₂ R seed hseed W K hK
  have hh := hbound hcard a b ha hb s p h₁ h₂ R seed hseed
    ((K : ℂ)*paperRadialFourier W 0)
  conv at hh => rhs; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK]
  rw [zeroControl,singleton_control]
  convert hh using 1; ring

/-- The base, profiles, heights, masks, radius, and seed are all live after
one source constant. Seed and raw-volume caps are structural source gates. -/
theorem actual_second_zero_power (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι ≤ N → ∀ (a b : ℝ), 0 < a → 0 ≤ b →
    ∀ (s : Input ι) (p : Profiles a b), s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ)) (Z r B s₀ : ℝ),
    1 ≤ Z → volume s.toData ≤ Z^B → Z^s₀ ≤ (seed.absNorm : ℝ) →
    ‖((Z^r : ℝ) : ℂ)*paperRadialFourier W 0*
      sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) s.η s.t‖/volume s.toData ≤
      C*zeroControl s p ε*‖paperRadialFourier W 0‖*Z^(r+ε*B-s₀) := by
  obtain ⟨C,hC,hbound⟩ := actual_second_zero_radius N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard a b ha hb s p h₁ h₂ R seed hseed W Z r B s₀ hZ hvol hseedN
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hzn : 0 < Z^s₀ := Real.rpow_pos_of_pos hz _
  have hp := Real.rpow_le_rpow (volume_pos s.toData).le hvol hε.le
  rw [←Real.rpow_mul hz.le] at hp
  have hc := zeroControl_nonneg s p ε
  have hh := hbound hcard a b ha hb s p h₁ h₂ R seed hseed W (Z^r)
    (Real.rpow_pos_of_pos hz _)
  apply hh.trans
  calc
    _ ≤ C*zeroControl s p ε*‖paperRadialFourier W 0‖*Z^r*Z^(B*ε)/Z^s₀ := by
      apply div_le_div₀ (by positivity) _ hzn hseedN
      gcongr
    _ = _ := by
      calc
        _ = (C*zeroControl s p ε*‖paperRadialFourier W 0‖)*(Z^r*Z^(B*ε)/Z^s₀) := by ring
        _ = (C*zeroControl s p ε*‖paperRadialFourier W 0‖)*Z^(r+B*ε-s₀) := by
          rw [←Real.rpow_add hz,←Real.rpow_sub hz]
        _ = _ := by congr 1; congr 1; ring

end
end OAI.SevenEighths.Cycle61SecondZero
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_second_zero_radius
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_second_zero_power
#print axioms OAI.SevenEighths.Cycle61SecondZero.zeroControl_nonneg
#print axioms OAI.SevenEighths.Cycle61SecondZero.singleton_control

end
/- END ORIGINAL Cycle61.Physical.SecondZero.Source -/
