import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryExceptionalScalar
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorActiveInput
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryExceptionalBudget
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialSourceReduction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Cycle63Moment HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSecondEnergySplit RayFourExpansion
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentSecondExceptionalFamily
open CenteredMomentCommonProfile ConcretePrimeRowBridge CenteredMomentActive
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstMixedRoot CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildSourceCaps
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def geometryExceptionalVolume {α : Type*} [Fintype α] (d : Input α) : ℝ :=
  CenteredMomentExceptionalAmplitudePair.volume d.toData
local instance geometryExceptionalAggregateSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

section Main
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
variable (M Z ξ sigma reserve t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
variable (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin))
variable (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
private def geometryMainExceptionalReferenceCore (τ : Character) (I H E : Ideal O)
    (K X Z sigma delta reserve r : ℝ) : ℝ :=
  ((X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
    Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (H.absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I H}).absNorm:ℝ)) 0/6)))*
    (X/(I.absNorm:ℝ))^(1/3:ℝ)*
    (mainCommonRadius Z (Real.logb Z (H.absNorm:ℝ)) (nominalLog I H E K X Z)
      (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^(5/6:ℝ)*Z^(-sigma/3)*
    Z^(-2*max r 0/3)

private theorem geometry_main_exceptional_reference_core_eq (τ : Character) (I H E : Ideal O)
    (K X Z sigma delta reserve r : ℝ) :
    geometryMainExceptionalReferenceCore τ I H E K X Z sigma delta reserve r=
      geometryExceptionalMainReference τ I H E K X Z sigma delta reserve r := by
  dsimp only [geometryMainExceptionalReferenceCore,geometryExceptionalMainReference]
  ring

/-- The literal actual main-child reference, with its actual input minimum. -/
def geometryMainExceptionalReferenceActual : ℝ :=
  let src := geometryFirstSource s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
  let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  geometryMainExceptionalReferenceCore τ I (if reflected then src.C else src.D)
    (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
    (Z^M) (geometryExceptionalVolume s) Z sigma (frequencyLoss Z 32 ξ) reserve
    (inputCap Z (child s I R B τ t))

omit [DecidableEq ι] in
/-- Orientation transport is arithmetic. It uses the swapped inactive subset,
not an assumption about the exceptional energy or its prefactor. -/
theorem actual_geometry_main_exceptional_reference_bound (plainLoss : ℝ)
    (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
    (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
    (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
    (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂) :
    geometryMainExceptionalReferenceActual reflected s R seed M Z ξ sigma reserve t hZ bin j B≤
      Z^(Real.logb Z (geometryExceptionalVolume s)-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3) := by
  let src := (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1)
  have hklog : Real.logb Z (Z^M)=M := Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hm := actual_geometry_column_modulus reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  cases reflected
  · have hh := actual_main_child_exceptional_reference s.η (geometryColumnCharacter false s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) src.C src.D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
      src.hC src.hD src.sameSupport src.inactive rfl s R B (Z^M) Z sigma
      (frequencyLoss Z 32 ξ) reserve t plainLoss (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    change geometryMainExceptionalReferenceCore _ _ _ _ _ _ _ _ _ _ _≤_ 
    rw [geometry_main_exceptional_reference_core_eq]
    exact hh

  · have hm' : (geometryColumnCharacter true s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.D src.C=>P.val)
          (swapSubset src.C src.D src.inactive)*activeConductor src.D src.C} := by
      rw [swapped_modulus_factor]
      exact hm
    have hh := actual_main_child_exceptional_reference s.η (geometryColumnCharacter true s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) src.D src.C
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
      src.hD src.hC src.sameSupport.symm (swapSubset src.C src.D src.inactive)
      (by rw [swapSubset_generator]) s R B (Z^M) Z sigma
      (frequencyLoss Z 32 ξ) reserve t plainLoss (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm'
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    change geometryMainExceptionalReferenceCore _ _ _ _ _ _ _ _ _ _ _≤_
    rw [geometry_main_exceptional_reference_core_eq]
    exact hh

set_option linter.defProp false in
set_option linter.unnecessarySeqFocus false in
/-- The actual weighted whole exceptional energy pays the original-slot
profile control. The first projector seed and physical side remain visible.
The proof-valued definition infers its actual dependent statement. -/
def actual_geometry_main_exceptional_paid
    (wlo whi : ℝ) (p : Profiles wlo whi) (ε δ θ Bcap L Cr : ℝ)
    (J : ℕ) (Sp : Finset (ℕ×ℕ)) (Ck : ℝ) (Qfix : Ideal O) (Kfix : ℝ)
    (hKfix : 0≤Kfix) (hCk : 0≤Ck)
    (N : ℕ) (b : ℝ) (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
    :=
    let I := (geometryColumnIdeal reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
    let τ := (geometryColumnCharacter reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
    let u := child s I R B τ t
    let src := (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1)
    let Kmain := (firstMainRadius reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve (geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
    fun (hest : geometryExceptionalSourceEstimate wlo whi u.lo u.hi W ε δ θ Bcap L Cr
      J Sp Ck Qfix Kfix Z)
    (hP : ∀i,1≤u.P i) (hp₁ : u.W₁=p.profile 0) (hp₂ : u.W₂=p.profile 1)
    (hR : R*I≠0) (hseed : Squarefree j.2.1.val) (hseed0 : j.2.1.val≠0)
    (hcap : sourceRadius u≤Z^Bcap) (χ₀ : RayCharacter) (m : O)
    (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Tsec : ℝ)
    (hF : 0<frequencyRadius Tsec Z ξ) (hFc : frequencyRadius Tsec Z ξ≤Cr*Z^L)
    (hcond : (expandedFactor u.η:ℝ)*(R*I).absNorm*(sourceRadius u)^2*
      (4*frequencyRadius Tsec Z ξ)≤Z^Bcap)
    (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0)=>
    have hparentV : 0<geometryExceptionalVolume s :=
      CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
    have hchildV : 0<geometryExceptionalVolume u :=
      CenteredMomentExceptionalAmplitudePair.volume_pos u.toData
    have hI := norm_pos I (allocation_ne s I B)
    have hfixed := fixedPresentationCost_pos
    have hrad := norm_pos (commonRadical
      src.C
      src.D)
      (commonRadical_ne_zero _ _)
    have hτ := norm_pos (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus_ne_bot
    have hbn : 0≤b^N := pow_nonneg (zero_le_one.trans hb) _
    have hbase : 0≤((∏i,u.lo i)*wlo*wlo) := by
      rw [mul_assoc,←sq]
      exact mul_nonneg (Finset.prod_nonneg (fun i _=>u.lo_pos i |>.le)) (sq_nonneg wlo)
    have hlower := Real.rpow_nonneg hbase (-2/3:ℝ)
    have hmin := input_cap_scales Z hZ u
    have he := hest u p (fun _=>rfl) (fun _=>rfl) hP hp₁ hp₂
      (R*I) j.2.1.val hR hseed hseed0 hcap χ₀ m hm hml hm2 Tsec ξ Kmain
      (first_main_radius_pos reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve
        (zero_lt_one.trans hZ) (geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)) hF hFc hcond (inputCap Z u)
      hmin.1 hmin.2.1 hmin.2.2.1 hmin.2.2.2
    have hw := actual_geometry_exceptional_allocation_weight reflected s R seed W M Z ξ hZ
      a₁ a₂ ha₁ ha₂ hs₁ hs₂ bin j N b B
    have hp := actual_child_exceptional_profile_payment Sp p J Qfix Kfix hKfix
      N b hb s hu hc I R B τ t
    have hv := common_volume_le N b hb s hc hu I R B τ t hne
    have hvol : (geometryExceptionalVolume u)^(1/3:ℝ)≤(b^N)^(1/3:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ))^(1/3:ℝ) := by
      have hi := norm_pos I (allocation_ne s I B)
      calc
        _≤(b^N*geometryExceptionalVolume s/(I.absNorm:ℝ))^(1/3:ℝ) :=
          Real.rpow_le_rpow hchildV.le hv (by norm_num)
        _=_ := by rw [mul_div_assoc,Real.mul_rpow (by positivity) (by positivity)]
    have hzero : 0≤‖partEnergy true u.η χ₀ Qfix m u.t
        (finiteColumns (Fintype.piFinset u.pools)) (coefficient u (R*I) j.2.1.val)
        W Kmain Tsec Z ξ (sourceRadius u)‖/geometryExceptionalVolume u :=
      div_nonneg (norm_nonneg _) hchildV.le
    let U := (if reflected then 1/(src.D.absNorm:ℝ)
      else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ))*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/(commonRadical src.C src.D).absNorm)*
      ((geometryExceptionalVolume s/(I.absNorm:ℝ))/
        ((τ.modulus.absNorm:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ))^2*
          Z^(if reflected then max (3*geometryExponents s R seed (Z^M) Z ξ j.1.val 1-
            5*geometryExponents s R seed (Z^M) Z ξ j.1.val 0-
            geometryExponents s R seed (Z^M) Z ξ j.1.val 3) 0/6 else
            max (3*geometryExponents s R seed (Z^M) Z ξ j.1.val 0-
            5*geometryExponents s R seed (Z^M) Z ξ j.1.val 1-
            geometryExponents s R seed (Z^M) Z ξ j.1.val 3) 0/6)))
    let A := (max 1 b)^N*((actualAllocations s.pools I).card:ℝ)
    let F := (frozenControl B.val s.M)^2
    let Pf := profileFactor Sp u p J Qfix Kfix
    let Ppaid := CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix*
      p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6
    let Vc := (geometryExceptionalVolume u)^(1/3:ℝ)
    let Vb := (b^N)^(1/3:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ))^(1/3:ℝ)
    let Dpaid := Ck*Z^(2*ε+2*δ+2*Bcap*θ+sigma/3)*Z^(-sigma/3)*
      Z^(-2*max (inputCap Z u) 0/3)*
      Kmain^(5/6:ℝ)*((∏i,u.lo i)*wlo*wlo)^(-2/3:ℝ)/(j.2.1.val.absNorm:ℝ)
    let E := ‖partEnergy true u.η χ₀ Qfix m u.t (finiteColumns (Fintype.piFinset u.pools))
      (coefficient u (R*I) j.2.1.val) W Kmain Tsec Z ξ (sourceRadius u)‖/geometryExceptionalVolume u
    have hside : 0≤(if reflected then 1/(src.D.absNorm:ℝ)
      else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ)) := by split_ifs <;> positivity
    have hU : 0≤U := by
      dsimp only [U]
      exact mul_nonneg (mul_nonneg hside
        (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le))
        (div_nonneg (div_nonneg hparentV.le hI.le)
          (mul_nonneg (mul_nonneg hτ.le (sq_nonneg _))
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
    have hA : 0≤A :=
      mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _)
        (Nat.cast_nonneg _)
    have hD : 0≤Dpaid := by
      dsimp only [Dpaid]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg hCk (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (first_main_radius_pos reflected (Z^M) (geometryExceptionalVolume s)
          Z ξ sigma reserve (zero_lt_one.trans hZ)
          (geometryFirstLabel s R seed (Z^M) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)).le _)) hlower)
        (Nat.cast_nonneg _)
    have hPf : 0≤Pf := profileFactor_nonneg Sp u p J Qfix Kfix hKfix
    have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (geometryExceptionalVolume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
      (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j B≤U*A*F := by
      convert hw using 1 <;> dsimp only [U,A,F,geometryExceptionalVolume] <;> ring
    have hpower : Z^(2*ε+2*δ+2*Bcap*θ-2*max (inputCap Z u) 0/3)=
      Z^(2*ε+2*δ+2*Bcap*θ+sigma/3)*Z^(-sigma/3)*Z^(-2*max (inputCap Z u) 0/3) := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 1
      ring
    have he0 : E≤Dpaid*Pf*Vc := by
      have hh := he
      conv_rhs at hh => arg 1;arg 1;arg 1;arg 1;arg 2;rw [hpower]
      convert hh using 1 <;> dsimp only [E,Dpaid,Pf,Vc,geometryExceptionalVolume] <;> ring
    have hp0 : F*Pf≤Ppaid := hp
    have hv0 : Vc≤Vb := hvol
    have hq := mul_le_mul hp0 hv0 (Real.rpow_nonneg hchildV.le _) 
      ((mul_nonneg (sq_nonneg (frozenControl B.val s.M)) hPf).trans hp0)
    have hpaid := mul_le_mul hw0 he0 hzero
      (mul_nonneg (mul_nonneg hU hA) (sq_nonneg _))
    have hfinal : (U*A*F)*(Dpaid*Pf*Vc)≤(U*A*Dpaid)*(Ppaid*Vb) := by
      convert mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg hU hA) hD) using 1 <;> ring
    hpaid.trans hfinal

end Main

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
