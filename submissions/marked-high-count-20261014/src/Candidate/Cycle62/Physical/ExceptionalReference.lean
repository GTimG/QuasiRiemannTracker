import Candidate.Cycle62.Physical.TerminalRadius
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalLow
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle62ExceptionalReference
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
    (hK:0<K)(hV:0<V)(hZ:1<Z)
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
    (K X Z j sigma delta reserve r plainLoss : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X)
    (hrange : (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-
      Real.logb Z (I.absNorm:ℝ)-plainLoss≤r) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+4*sigma/3+5*(delta+reserve)/6+2*plainLoss/3):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=Cycle62.Physical.actual_main_side_saving η τ fixedBadMask I J E hI hJ A
    K X Z j (sigma/3) delta reserve hZ hmod
  have hsigma : 3*(sigma/3)=sigma := by ring
  simp only [hsigma] at hs
  simp only [hc,hd] at hs
  have he:=(actual_side_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) (max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0<mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
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
    (E:Finset (CommonIndex C D))(K V Z j g Bside:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
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
  have hz:0<Z:=zero_lt_one.trans hZ
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
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
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
    (K X Z j sigma delta reserve r plainLoss : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X)
    (hrange : (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4-
      Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k-plainLoss≤r) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (J.absNorm:ℝ)-Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+3*sigma/2+5*(delta+reserve)/6+2*plainLoss/3):=by
  have hz:0<Z:=zero_lt_one.trans hZ
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
  have hrad:0<errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith [le_max_left r 0]

end SevenEighths.Cycle62ExceptionalReference
end
end OAI
#print axioms OAI.SevenEighths.Cycle62ExceptionalReference.actual_main_side_exceptional_reference

#print axioms OAI.SevenEighths.Cycle62ExceptionalReference.actual_error_side_exceptional_reference
