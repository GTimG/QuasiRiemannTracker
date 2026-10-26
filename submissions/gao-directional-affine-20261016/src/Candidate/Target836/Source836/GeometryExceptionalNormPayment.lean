import Candidate.Target836.Source836.GlobalNamed
import Candidate.Target836.Error836.GeometryAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalErrorFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryContraction

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
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
open Filter CenteredMomentLogDyadic CenteredMomentFirstAnnularInput CenteredMomentAmplificationRadicalFamily
open CenteredMomentChildRows CenteredMomentAmplificationActiveFactor CenteredMomentAllocationCost
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance exceptionalNormPaymentSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

private theorem exceptional_norm_mass_nonneg (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) :
    0≤exceptionalPhysicalNormSum η χ Q m t S β W K Tsec Z ξ H := by
  unfold exceptionalPhysicalNormSum
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro U _
  apply Finset.sum_nonneg
  intro n _
  exact norm_nonneg _

attribute [local irreducible] exceptionalPhysicalNormSum

section Main
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O) (Ψ W : 𝓢(ℝ,ℂ))
variable (M Z ξ sigma reserve t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
variable (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin))
variable (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
set_option linter.defProp false in
set_option linter.unnecessarySeqFocus false in
/-- The actual weighted positive exceptional physical-block mass pays the original-slot
profile control. The first projector seed and physical side remain visible.
The proof-valued definition infers its actual dependent statement. -/
def actual_geometry_main_exceptional_norm_paid
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
    fun (hest : geometryExceptionalNormSourceEstimate wlo whi u.lo u.hi W ε δ θ Bcap L Cr
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
    have hw := actual_geometry_exceptional_allocation_weight reflected s R seed Ψ M Z ξ hZ
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
    have hzero : 0≤exceptionalPhysicalNormSum u.η χ₀ Qfix m u.t
        (finiteColumns (Fintype.piFinset u.pools)) (coefficient u (R*I) j.2.1.val)
        W Kmain Tsec Z ξ (sourceRadius u)/geometryExceptionalVolume u :=
      by
      apply div_nonneg _ hchildV.le
      exact exceptional_norm_mass_nonneg ..
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
    let E := exceptionalPhysicalNormSum u.η χ₀ Qfix m u.t (finiteColumns (Fintype.piFinset u.pools))
      (coefficient u (R*I) j.2.1.val) W Kmain Tsec Z ξ (sourceRadius u)/geometryExceptionalVolume u
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
      (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ q)) N b j B≤U*A*F := by
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

set_option linter.defProp false in
set_option linter.unnecessarySeqFocus false in
/-- The literal twice-child exceptional physical-block mass pays both common-allocation
controls. The prime cost and true prime-power volume remain explicit.
The proof-valued definition infers its actual dependent statement. -/
def actual_geometry_error_exceptional_norm_paid
    (wlo whi : ℝ) (p0 : Profiles wlo whi) (ε δ θ Bcap L Cr : ℝ)
    (J : ℕ) (Sp : Finset (ℕ×ℕ)) (Ck : ℝ) (Qfix : Ideal O) (Kfix : ℝ)
    (hKfix : 0≤Kfix) (hCk : 0≤Ck)
    (N : ℕ) (b : ℝ) (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x) :=
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let u1 := child s I R B τ t
    let src := geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
    let gv := geometryExponents s R seed (Z^M) Z ξ j.1.val
    let S := if reflected then max (3*gv 1-5*gv 0-gv 3) 0/6
      else max (3*gv 0-5*gv 1-gv 3) 0/6
    fun (p : O) (hp : p≠0) (k : ℕ)
      (Bp : actualAllocations u1.pools ((Ideal.span {p})^k)) (υ : Character) (v : ℝ)
      (hslot : ∀i,∀Q∈u1.slots i,IsCoprime (Ideal.span {p}) Q) =>
    let Q := Ideal.span {p}
    let u := twiceChild s I R B τ t Q k Bp υ v
    let Kerror := errorCommonRadius Z
      (Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ))
      (nominalLog src.C src.D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
        (Z^M) (geometryExceptionalVolume s) Z)
      (Real.logb Z (I.absNorm:ℝ)) sigma (frequencyLoss Z 32 ξ) reserve p k
    fun (hest : geometryExceptionalNormSourceEstimate wlo whi u.lo u.hi W ε δ θ Bcap L Cr
      J Sp Ck Qfix Kfix Z)
      (hP : ∀i,1≤u.P i) (hp₁ : u.W₁=p0.profile 0) (hp₂ : u.W₂=p0.profile 1)
      (hR : (R*I)*(Q^k)≠0) (hseed : Squarefree j.2.1.val) (hseed0 : j.2.1.val≠0)
      (hcap : sourceRadius u≤Z^Bcap) (χ₀ : RayCharacter) (m : O)
      (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Tsec : ℝ)
      (hF : 0<frequencyRadius Tsec Z ξ) (hFc : frequencyRadius Tsec Z ξ≤Cr*Z^L)
      (hcond : (expandedFactor u.η:ℝ)*((R*I)*(Q^k)).absNorm*(sourceRadius u)^2*
        (4*frequencyRadius Tsec Z ξ)≤Z^Bcap)
      (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0) =>
    have hparentV : 0<geometryExceptionalVolume s :=
      CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
    have hchildV : 0<geometryExceptionalVolume u :=
      CenteredMomentExceptionalAmplitudePair.volume_pos u.toData
    have hfixed := fixedPresentationCost_pos
    have hrad := norm_pos (commonRadical src.C src.D) (commonRadical_ne_zero _ _)
    have hτ := norm_pos τ.modulus τ.modulus_ne_bot
    have hI := norm_pos I (allocation_ne s I B)
    have hQ : Q≠(0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hp
    have hNQ := norm_pos Q hQ
    have hBpone (i) : Bp.val (Sum.inl i)=1 :=
      CenteredMomentAmplificationAllocationCost.allocation_slot_one u1.pools Q hQ k
        (fun i D hd=>⟨u1.pools_ne (Sum.inl i) D hd,hslot i D hd⟩) Bp i
    have hfBp : frozenControl Bp.val u1.M=1 := by
      dsimp only [frozenControl]
      simp only [hBpone,ne_eq,not_true_eq_false,Finset.filter_false,Finset.prod_empty]
    have hbn : 0≤b^N := pow_nonneg (zero_le_one.trans hb) _
    have hcost := localErrorCost_nonneg p (k-1)
    have hbase : 0≤((∏i,u.lo i)*wlo*wlo) := by
      rw [mul_assoc,←sq]
      exact mul_nonneg (Finset.prod_nonneg (fun i _=>(u.lo_pos i).le)) (sq_nonneg wlo)
    have hlower := Real.rpow_nonneg hbase (-2/3:ℝ)
    have hmin := input_cap_scales Z hZ u
    have he := hest u p0 (fun _=>rfl) (fun _=>rfl) hP hp₁ hp₂ ((R*I)*(Q^k))
      j.2.1.val hR hseed hseed0 hcap χ₀ m hm hml hm2 Tsec ξ Kerror
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hF hFc hcond
      (inputCap Z u) hmin.1 hmin.2.1 hmin.2.2.1 hmin.2.2.2
    have hw := actual_geometry_exceptional_allocation_weight reflected s R seed Ψ M Z ξ hZ
      a₁ a₂ ha₁ ha₂ hs₁ hs₂ bin j N b B
    have hp := actual_twice_exceptional_profile_payment Sp p0 J Qfix Kfix hKfix
      N b hb s hu hc I R B τ t Q k Bp υ v
    have hp' : (frozenControl B.val s.M)^2*profileFactor Sp u p0 J Qfix Kfix≤
        CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix*
          p0.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6 := by
      have hh := hp
      change (frozenControl B.val s.M)^2*(frozenControl Bp.val u1.M)^2*
        profileFactor Sp u p0 J Qfix Kfix≤_ at hh
      rw [hfBp,one_pow,mul_one] at hh
      exact hh
    have hv1 := common_volume_le N b hb s hc hu I R B τ t hne
    have hv : geometryExceptionalVolume u≤b^N*geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k := by
      change CenteredMomentAmplificationChildInput.volume (twiceChild s I R B τ t Q k Bp υ v)≤_
      rw [twiceChild,child_volume _ Q hQ k hslot]
      exact div_le_div_of_nonneg_right hv1 (pow_nonneg hNQ.le k)
    have hvol : (geometryExceptionalVolume u)^(1/3:ℝ)≤
        (b^N)^(1/3:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k)^(1/3:ℝ) := by
      calc
        _≤(b^N*geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k)^(1/3:ℝ) :=
          Real.rpow_le_rpow hchildV.le hv (by norm_num)
        _=_ := by
          rw [mul_div_assoc,mul_div_assoc,Real.mul_rpow hbn
            (div_nonneg (div_nonneg hparentV.le hI.le) (pow_nonneg hNQ.le k))]
    have hzero : 0≤exceptionalPhysicalNormSum u.η χ₀ Qfix m u.t
        (finiteColumns (Fintype.piFinset u.pools)) (coefficient u ((R*I)*(Q^k)) j.2.1.val)
        W Kerror Tsec Z ξ (sourceRadius u)/geometryExceptionalVolume u :=
      by
      apply div_nonneg _ hchildV.le
      exact exceptional_norm_mass_nonneg ..
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
    let Pf := profileFactor Sp u p0 J Qfix Kfix
    let Ppaid := CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix*
      p0.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6
    let Vc := (geometryExceptionalVolume u)^(1/3:ℝ)
    let Vb := (b^N)^(1/3:ℝ)*(geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k)^(1/3:ℝ)
    let Dpaid := Ck*Z^(2*ε+2*δ+2*Bcap*θ-2*max (inputCap Z u) 0/3)*
      Kerror^(5/6:ℝ)*((∏i,u.lo i)*wlo*wlo)^(-2/3:ℝ)/(j.2.1.val.absNorm:ℝ)
    let E := exceptionalPhysicalNormSum u.η χ₀ Qfix m u.t (finiteColumns (Fintype.piFinset u.pools))
      (coefficient u ((R*I)*(Q^k)) j.2.1.val) W Kerror Tsec Z ξ (sourceRadius u)/geometryExceptionalVolume u
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
      exact div_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg hCk (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) _)) hlower)
        (Nat.cast_nonneg _)
    have hPf : 0≤Pf := profileFactor_nonneg Sp u p0 J Qfix Kfix hKfix
    have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (geometryExceptionalVolume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
      (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ q)) N b j B≤U*A*F := by
      convert hw using 1 <;> dsimp only [U,A,F,geometryExceptionalVolume] <;> ring
    have he0 : E≤Dpaid*Pf*Vc := by
      convert he using 1 <;> dsimp only [E,Dpaid,Pf,Vc,geometryExceptionalVolume] <;> ring
    have hp0 : F*Pf≤Ppaid := hp'
    have hv0 : Vc≤Vb := hvol
    have hq := mul_le_mul hp0 hv0 (Real.rpow_nonneg hchildV.le _) 
      ((mul_nonneg (sq_nonneg (frozenControl B.val s.M)) hPf).trans hp0)
    have hwcost := mul_le_mul_of_nonneg_right hw0 hcost
    have hpaid := mul_le_mul hwcost he0 hzero
      (mul_nonneg (mul_nonneg (mul_nonneg hU hA) (sq_nonneg _)) hcost)
    have hfinal : (U*A*F*localErrorCost p (k-1))*(Dpaid*Pf*Vc)≤
        (U*A*Dpaid*localErrorCost p (k-1))*(Ppaid*Vb) := by
      convert mul_le_mul_of_nonneg_left hq
        (mul_nonneg (mul_nonneg (mul_nonneg hU hA) hD) hcost) using 1 <;> ring
    hpaid.trans hfinal

end Main

set_option linter.defProp false in
/-- Saved whole-source constants and actual admission close the literal
main allocation payment. Only original source and profile receipts remain
as inputs; the exceptional energy estimate is constructed here. -/
def actual_geometry_main_exceptional_norm_closed
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs) :=
  let hsave := actual_geometry_saved_exceptional_norm_sources wlo whi hwlo hwhi lo hi W
    ε δ θ 41 8 1 hε hδ hθ (by norm_num) (by norm_num) (by norm_num)
  let J := Classical.choose hsave
  let hj := Classical.choose_spec hsave
  let Sp := Classical.choose hj
  let hsp := Classical.choose_spec hj
  let Ck := Classical.choose hsp
  let hc := Classical.choose_spec hsp
  (J,Sp,Ck,fun (Qfix : Ideal O) hQ hQt hQ72=>
    let hk := hc.2 Qfix hQ hQt hQ72
    let Kfix := Classical.choose hk
    let hK := Classical.choose_spec hk
    (Kfix,PLift.up (And.intro hK.1
      (Filter.Eventually.mono (hK.2.and
        (eventual_actual_geometry_main_exceptional_admission (ι:=ι) η N b bs hb hbs))
        (fun Z hz=>And.intro hz.1.1
          (fun (hZ : 1<Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤N) (hend : Endpoints b bs bs s)
            (hsP : ∀i,1≤ s.P i) (p : Profiles wlo whi)
            (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤Z^(2:ℝ)) (hsource : sourceRadius s≤Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤Z) (M ξ sigma reserve t : ℝ)
            (hKM : Z^M≤Z) (hξ : 0≤ξ) (hξ₁ : ξ≤1)
            (hsigma : 0≤ sigma) (hreserve : 0≤reserve)
            (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
            (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
            (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (bin : ℤ×(Fin 5→ℤ))=>
          let hKMpos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
          fun (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ hKMpos bin)
            (hne : frozenCoefficient q.2.val
              (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hKMpos bin q.1.val)
              R s.ν s.W s.P≠0) (χ₀ : RayCharacter) (m : O)
            (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
          let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hKMpos bin q.1.val
          let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hKMpos bin q.1.val
          let hadmit := hz.2.2 reflected s R seed (Z^M) ξ sigma reserve t hKMpos
            hη hcard hend hs hz₁ hz₂ hV hsource hRN hKM hξ hξ₁ hsigma hreserve bin q hne
          let hest := (hz.1.2 s hlo hhi I R q.2 τ t).1
          let hseed := actual_first_live_squarefree
            (geometryFirstSource s R seed (Z^M) Z ξ hKMpos bin)
            (fun _=>logAnnulus) q.1.val q.1.property
          actual_geometry_main_exceptional_norm_paid reflected s R seed Ψ W M Z ξ sigma reserve t
            hZ bin q.1.val q.2 wlo whi p ε δ θ 41 8 1 J Sp Ck Qfix Kfix hK.1.le hc.1
            N b hb hend.1 hcard a₁ a₂ ha₁ ha₂ hs₁ hs₂ hest
            (fun i=>hsP i.val) hW₁ hW₂ (mul_ne_zero hR (allocation_ne s I q.2))
            hseed hseed.ne_zero hadmit.2.2.1 χ₀ m hm hml hm2
            (firstMainFourierScale reflected (Z^M) (volume s) Z ξ sigma reserve b N
              (geometryFirstLabel s R seed (Z^M) Z ξ hKMpos bin q.1.val))
            hadmit.1 (by simpa only [one_mul] using hadmit.2.1) hadmit.2.2.2 hne))))))

set_option linter.defProp false in
set_option backward.isDefEq.respectTransparency false in
/-- The saved estimate and arithmetic admission also close the literal
lifted active prime-error payment, with its original projector seed and
local prime cost. The active menu is fixed before any row sum. -/
def actual_geometry_error_exceptional_norm_closed
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs) :=
  let hsave := actual_geometry_saved_exceptional_norm_sources wlo whi hwlo hwhi lo hi W
    ε δ θ 126 25 1 hε hδ hθ (by norm_num) (by norm_num) (by norm_num)
  let J := Classical.choose hsave
  let hj := Classical.choose_spec hsave
  let Sp := Classical.choose hj
  let hsp := Classical.choose_spec hj
  let Ck := Classical.choose hsp
  let hc := Classical.choose_spec hsp
  (J,Sp,Ck,fun (Qfix : Ideal O) hQ hQt hQ72=>
    let hk := hc.2 Qfix hQ hQt hQ72
    let Kfix := Classical.choose hk
    let hK := Classical.choose_spec hk
    let hbound := hK.2.and
      (eventual_actual_geometry_error_exceptional_admission (ι:=ι) η N b bs hb hbs)
    (Kfix,PLift.up (And.intro hK.1 hbound),
      PLift.up (fun (Z : ℝ) (hz : geometryExceptionalEventualPredicate hbound Z)=>
          let hpayed := (fun (hZ : 1<Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤N) (hend : Endpoints b bs bs s)
            (hsP : ∀i,1≤ s.P i) (p0 : Profiles wlo whi)
            (hW₁ : s.W₁=p0.profile 0) (hW₂ : s.W₂=p0.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤Z^(2:ℝ)) (hsource : sourceRadius s≤Z^(3:ℝ))
            (hlogV : |Real.logb Z (volume s)|≤3) (hRN : (R.absNorm:ℝ)≤Z)
            (amp ξ reserve t : ℝ) (ha : 0≤amp) (ha₁ : amp≤1)
            (hξ : 0≤ξ) (hξ₁ : ξ≤1) (hreserve : 0≤reserve)
            (hω : frequencyLoss Z 32 ξ+reserve≤3)
            (a₁ a₂ : ℝ) (ha₁p : 0<a₁) (ha₂p : 0<a₂)
            (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
            (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (bin : ℤ×(Fin 5→ℤ))=>
          let hKMpos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
          fun (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin)
            (hne : frozenCoefficient q.2.val
              (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val)
              R s.ν s.W s.P≠0) (p : O) (hp : p≠0)
            (hpN : ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ))
            (hslot : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
              hKMpos bin t q).slots j→IsCoprime (Ideal.span {p}) I) (i : Fin 3)
            (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
              (Z^(1:ℝ)) Z ξ hKMpos bin t q)).pools ((Ideal.span {p})^(errorIndex i+1)))
            (υ : Character) (χ : RayCharacter) (v : ℝ)
            (hυ : υ.modulus.absNorm≤radicalBound (childCharacter
              (geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val) χ)
                fixedBadMask p (errorMovingExponent (errorIndex i)))
            (χ₀ : RayCharacter) (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
          let I := geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val
          let τ := geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val
          let Q := Ideal.span {p}
          let Bplift := geometryExceptionalActiveLift reflected s R seed Z ξ t hZ bin q p i Bp
          let hadmit := hz.2.2 reflected s R seed amp ξ reserve t hZ hη hcard hend hs hz₁ hz₂
            hV hsource hlogV hRN ha ha₁ hξ hξ₁ hreserve hω bin q hne p hp hpN hslot i Bp υ χ v hυ
          let hest := (hz.1.2 s hlo hhi I R q.2 τ t).2 Q (errorIndex i+1) Bplift υ v
          let hseed := actual_first_live_squarefree
            (geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hKMpos bin)
            (fun _=>logAnnulus) q.1.val q.1.property
          actual_geometry_error_exceptional_norm_paid reflected s R seed Ψ W 1 Z ξ (3*amp) reserve t
            hZ bin q.1.val q.2 wlo whi p0 ε δ θ 126 25 1 J Sp Ck Qfix Kfix hK.1.le hc.1
            N b hb hend.1 hcard a₁ a₂ ha₁p ha₂p hs₁ hs₂ p hp (errorIndex i+1) Bplift υ v hslot
            hest (fun j=>hsP j.val.val) hW₁ hW₂
            (mul_ne_zero (mul_ne_zero hR (allocation_ne s I q.2))
              (pow_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr hp)))
            hseed hseed.ne_zero hadmit.2.2.1 χ₀ m hm hml hm2
            (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ bin q p i)
            hadmit.1 (by simpa only [one_mul] using hadmit.2.1) hadmit.2.2.2 hne)
          And.intro hz.1.1 hpayed)))

/-- Every original allocation is summed, and cancelled frozen coefficients
contribute zero before the positive exceptional physical-block mass is normalized. -/
def geometryExceptionalMainNormRowMass (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (Ψ W : 𝓢(ℝ,ℂ)) (M Z ξ sigma reserve t : ℝ) (hZ : 1<Z)
    (N : ℕ) (b : ℝ) (bin : ℤ×(Fin 5→ℤ)) (Qfix : Ideal O)
    (χ₀ : RayCharacter) (m : O)
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin)) : ℝ :=
  let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let l := geometryFirstLabel s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  ∑B : actualAllocations s.pools I,
    if frozenCoefficient B.val I R s.ν s.W s.P≠0 then
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
        (Real.logb Z (geometryExceptionalVolume s))
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
        (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ q)) N b j B*
      (exceptionalPhysicalNormSum τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset (child s I R B τ t).pools))
        (coefficient (child s I R B τ t) (R*I) j.2.1.val) W
        (firstMainRadius reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve l)
        (firstMainFourierScale reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve b N l)
        Z ξ (sourceRadius (child s I R B τ t))/geometryExceptionalVolume (child s I R B τ t))
    else 0

private theorem full_main_fold_algebra
    (E S Shell F A Ck Cprof Pz lower L D Control bro q volumeRoot kr mr Rpow : ℝ)
    (hpaid : E≤S*F*q*A*(Ck*Pz*mr*kr*lower/D)*(Cprof*Control*bro*volumeRoot))
    (hside : S≤Shell) (hlower : lower≤L) (href : q*volumeRoot*kr*mr≤Rpow)
    (hS : 0≤S) (hShell : 0≤Shell) (hF : 0≤F) (hA : 0≤A)
    (hP : 0≤Pz) (hl : 0≤lower) (hL : 0≤L) (hD : 0≤D)
    (hc : 0≤Control) (hb : 0≤bro) (hq : 0≤q) (hi : 0≤volumeRoot)
    (hk : 0≤kr) (hm : 0≤ mr) :
    E≤Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*Control*bro*Rpow := by
  let rest := S*F*A*Pz*(lower/D)*Control*bro*(q*volumeRoot*kr*mr)
  have hrest : 0≤rest := by dsimp only [rest]; positivity
  calc
    E≤(Ck*Cprof)*rest := by convert hpaid using 1; dsimp only [rest]; ring
    _≤ max 1 (Ck*Cprof)*rest := mul_le_mul_of_nonneg_right (le_max_right _ _) hrest
    _≤ max 1 (Ck*Cprof)*(Shell*F*A*Pz*(L/D)*Control*bro*Rpow) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (le_max_left _ _))
      dsimp only [rest]
      gcongr
    _=_ := by ring

private theorem full_main_paid_fold_algebra
    (E S Shell F A Ck Cprof Pz lower L D c height mass bro q root kr m₁ m₂ Rpow : ℝ)
    (hpaid : E≤(S*F*q)*A*(Ck*Pz*m₁*m₂*kr*lower/D)*
      ((Cprof*c*height*mass)*(bro*root)))
    (hside : S≤Shell) (hlower : lower≤L) (href : q*root*kr*m₁*m₂≤Rpow)
    (hS : 0≤S) (hShell : 0≤Shell) (hF : 0≤F) (hA : 0≤A)
    (hP : 0≤Pz) (hl : 0≤lower) (hL : 0≤L) (hD : 0≤D)
    (hc : 0≤c*height*mass) (hb : 0≤bro) (hq : 0≤q) (hi : 0≤root)
    (hk : 0≤kr) (hm : 0≤ m₁*m₂) :
    E≤Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*(c*height*mass)*bro*Rpow := by
  exact full_main_fold_algebra E S Shell F A Ck Cprof Pz lower L D
    (c*height*mass) bro q root kr (m₁*m₂) Rpow
    (by convert hpaid using 1; ring) hside hlower
    (by convert href using 1; ring) hS hShell hF hA hP hl hL hD hc hb hq hi hk hm

set_option linter.defProp false in
/-- The complete supported main family derives its allocation costs from
the saved exceptional physical-block norm estimate. The original projector and radical
are paid jointly before all four dyads and both rays are counted. -/
def actual_geometry_main_exceptional_norm_full
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0< slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1) :=
  let closed := actual_geometry_main_exceptional_norm_closed wlo whi hwlo hwhi lo hi W
    ε δ θ hε hδ hθ η N b bs hb hbs
  let J := closed.1
  let Sp := closed.2.1
  let Ck := closed.2.2.1
  let halloc := actualAllocations_uniform_small_power (N+2) (εalloc/2) (half_pos hea)
  let Da := Classical.choose halloc
  let hDa := Classical.choose_spec halloc
  let hcolumns := eventual_actual_zero_column_payment (ι:=ι) 2 0 3
    (((N:ℝ)+2)*3) ξ εcount (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hξ hec
  let Cd := Classical.choose hcolumns
  let hCd := Classical.choose_spec hcolumns
  (J,Sp,Ck,fun (Qfix : Ideal O) hQ hQt hQ72=>
    let saved := closed.2.2.2 Qfix hQ hQt hQ72
    let Kfix := saved.1
    (Kfix,Cd,Da,PLift.up (And.intro saved.2.down.1 (And.intro hCd.1 (And.intro hDa.1
      (Filter.Eventually.mono (saved.2.down.2.and hCd.2)
        (fun Z hz=>And.intro hz.1.1
          (fun (hZ : 1<Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤N) (hend : Endpoints b bs bs s)
            (hlower : slotlo≤ s.lower) (hsP : ∀i,1≤ s.P i)
            (p : Profiles wlo whi) (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed) (hs0 : seed≠0)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤Z^(2:ℝ)) (hsourcepos : 0< sourceRadius s)
            (hsource : sourceRadius s≤Z^(3:ℝ))
            (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤Z) (M sigma reserve t plainLoss : ℝ)
            (hM : 0≤M) (hKM : Z^M≤Z) (hsigma : 0≤ sigma) (hreserve : 0≤reserve)
            (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
            (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
            (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
            (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂)
            (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
            (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
            (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (bin : ℤ×(Fin 5→ℤ))
            (χ₀ : RayCharacter) (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
          let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
          let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
            (fun _=>logAnnulus)
          by
          have hZpos : 0<Z := zero_lt_one.trans hZ
          let Hshell := Z^((bin.2 1:ℝ)*Real.logb Z 2)
          have hH : 0<Hshell := Real.rpow_pos_of_pos hZpos _
          have hphysical (j : rows) : Hshell≤
              ((geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1).D.absNorm:ℝ) ∧
              ((geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1).D.absNorm:ℝ)≤2*Hshell := by
            have hr := actual_geometry_fiber_range s R seed (Z^M) Z ξ 3 hZ hs hz₁ hz₂
              hsource bin j.val.1 1
            have hn := actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂
              hsource j.val.1.val 1
            have hl := Real.rpow_le_rpow_of_exponent_le hZ.le hr.1
            have hu := Real.rpow_le_rpow_of_exponent_le hZ.le hr.2.le
            rw [geometryExponents,Real.rpow_logb hZpos hZ.ne' (zero_lt_one.trans_le hn.1)] at hl hu
            have he : Z^(((bin.2 1:ℝ)+1)*Real.logb Z 2)=2*Hshell := by
              rw [add_mul,one_mul,Real.rpow_add hZpos,
                Real.rpow_logb hZpos hZ.ne' (by norm_num : (0:ℝ)<2)]
              exact mul_comm _ _
            exact ⟨hl,hu.trans_eq he⟩
          have hfixed : 0<fixedPresentationCost := fixedPresentationCost_pos
          let Control := p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6
          let Shell := if reflected then 1/Hshell
            else (4/((∏i,s.lo i)*a₁*a₂))^2*(2*Hshell)
          let coef := max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
            N b J Qfix Kfix)
          let factor := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
            coef*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Da^2
          let exponent := 2*ε+2*δ+2*41*θ+sigma/3+
            Real.logb Z (geometryExceptionalVolume s)-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
            4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3+3*εalloc
          let cost := fun j : rows=>geometryExceptionalMainNormRowMass reflected s R seed Ψ W
            M Z ξ sigma reserve t hZ N b bin Qfix χ₀ m j.val
          have hShell : 0≤Shell := by dsimp only [Shell]; split_ifs <;> positivity
          have hLower : 0≤geometryExceptionalLowerConstant N slotlo wlo :=
            Real.rpow_nonneg (by positivity) _
          have hControl : 0≤Control := by dsimp only [Control]; positivity
          have hfactor : 0≤factor := by dsimp only [factor,coef]; positivity
          have hc : ∀j : rows,0≤cost j := by
            intro j
            unfold cost geometryExceptionalMainNormRowMass
            apply Finset.sum_nonneg
            intro B _
            split_ifs
            · exact mul_nonneg (geometryAllocationWeight_nonneg ..)
                (div_nonneg (exceptional_norm_mass_nonneg ..) (CenteredMomentExceptionalAmplitudePair.volume_pos _).le)
            · exact le_rfl
          have hcost : ∀j : rows,cost j≤factor*
              Z^(exponent-geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)/
                (j.val.2.1.val.absNorm:ℝ) := by
            intro j
            let l := geometryFirstLabel s R seed (Z^M) Z ξ hK bin j.val
            let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.val
            let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin j.val
            let src := geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1
            let X := geometryExceptionalVolume s
            let Pz := Z^(2*ε+2*δ+2*41*θ+sigma/3)
            let Rpow := Z^(Real.logb Z X-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
              4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3)
            let rad := ((commonRadical src.C src.D).absNorm:ℝ)
            let Dproj := (j.val.2.1.val.absNorm:ℝ)
            let G := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
              coef*Pz*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Rpow
            have hG : 0≤G := by dsimp only [G,coef,Pz,Rpow]; positivity
            have hrad : 0<rad := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero _ _)
            have hDproj : 0<Dproj := CenteredMomentFirstScale.norm_pos _
              (actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
                (fun _=>logAnnulus) j.val j.property).ne_zero
            have hpoint (B : actualAllocations s.pools I)
                (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0) :
                geometryAllocationWeight reflected s R seed (Z^M) Z ξ M (Real.logb Z X) hK bin
                  (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ q)) N b j.val B*
                (exceptionalPhysicalNormSum τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset (child s I R B τ t).pools))
                  (coefficient (child s I R B τ t) (R*I) j.val.2.1.val) W
                  (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)
                  (firstMainFourierScale reflected (Z^M) X Z ξ sigma reserve b N l)
                  Z ξ (sourceRadius (child s I R B τ t))/geometryExceptionalVolume (child s I R B τ t))≤
                ((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
              let u := child s I R B τ t
              have hXpos : 0<X := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
              have hIpos : 0<(I.absNorm:ℝ) :=
                CenteredMomentFirstScale.norm_pos _ (allocation_ne s I B)
              have hτpos : 0<(τ.modulus.absNorm:ℝ) :=
                CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
              have hbase : 0≤(∏i,u.lo i)*wlo*wlo := mul_nonneg
                (mul_nonneg (Finset.prod_nonneg (fun i _=>(u.lo_pos i).le)) hwlo.le) hwlo.le
              let den := (τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
                Z^(max (3*Real.logb Z (I.absNorm:ℝ)-
                  5*Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
                  Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6)
              let qfac := (X/(I.absNorm:ℝ))/den
              let mr := Z^(-sigma/3)*Z^(-2*max (inputCap Z u) 0/3)
              let kr := (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)^(5/6:ℝ)
              let lower := ((∏i,u.lo i)*wlo*wlo)^(-2/3:ℝ)
              let side := if reflected then 1/(src.D.absNorm:ℝ)
                else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ)
              have hpayed := hz.1.2 hZ s hlo hhi hη hcard hend hsP p hW₁ hW₂ R seed hR hs
                hz₁ hz₂ hV hsource hRN M ξ sigma reserve t hKM hξ hξ₁ hsigma hreserve
                a₁ a₂ ha₁ ha₂ hs₁ hs₂ reflected Ψ bin (⟨j,B⟩ : GeometryLowFirstIndex
                  reflected s R seed (Z^M) Z ξ hK bin) hne χ₀ m hm hml hm2
              have hlogs :
                  (if reflected then max (3*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 1-
                    5*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 0-
                    geometryExponents s R seed (Z^M) Z ξ j.val.1.val 3) 0/6 else
                    max (3*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 0-
                    5*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 1-
                    geometryExponents s R seed (Z^M) Z ξ j.val.1.val 3) 0/6)=
                  max (3*Real.logb Z (I.absNorm:ℝ)-
                    5*Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
                    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6 := by
                cases reflected <;> rfl
              dsimp only at hpayed
              rw [hlogs] at hpayed
              have href := actual_geometry_main_exceptional_radius_bound reflected s R seed
                M Z ξ sigma reserve t hZ bin j.val B plainLoss hX₁ hX₂ hY₁ hY₂
              have hlow := actual_geometry_exceptional_lower_factor u N slotlo wlo
                ((live_card_le B.val).trans hcard) hslot hlower hwlo
              have hside : side≤Shell := by
                dsimp only [side,Shell]
                split_ifs
                · exact div_le_div_of_nonneg_left zero_le_one hH (hphysical j).1
                · exact mul_le_mul_of_nonneg_left (hphysical j).2 (sq_nonneg _)
              have hqfac : 0≤qfac := by dsimp only [qfac,den]; positivity
              have hside0 : 0≤ side := by dsimp only [side]; split_ifs <;> positivity
              let Enamed := geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
                (Real.logb Z X) hK bin (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ q))
                N b j.val B*
                (exceptionalPhysicalNormSum τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset u.pools))
                  (coefficient u (R*I) j.val.2.1.val) W
                  (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)
                  (firstMainFourierScale reflected (Z^M) X Z ξ sigma reserve b N l)
                  Z ξ (sourceRadius u)/geometryExceptionalVolume u)
              have hh := full_main_paid_fold_algebra Enamed side Shell
                (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/rad)
                ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)) Ck
                (CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
                Pz lower (geometryExceptionalLowerConstant N slotlo wlo) Dproj
                (p.control Sp^2) ((1+‖t‖)^(2*J)) ((∏i,s.M i)^6)
                ((b^N)^(1/3:ℝ)) qfac ((X/(I.absNorm:ℝ))^(1/3:ℝ)) kr
                (Z^(-sigma/3)) (Z^(-2*max (inputCap Z u) 0/3)) Rpow
                hpayed hside hlow href
                hside0 hShell
                (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le)
                (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _)
                  (Nat.cast_nonneg _))
                (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hbase _)
                hLower hDproj.le hControl
                (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hb) _) _)
                hqfac (Real.rpow_nonneg (div_nonneg hXpos.le hIpos.le) _)
                (Real.rpow_nonneg
                  (first_main_radius_pos reflected (Z^M) X Z ξ sigma reserve hZpos l).le _)
                (mul_nonneg (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hZpos.le _))
              convert hh using 1; dsimp only [Enamed,G,coef,Control,u]; ring
            have hrow : cost j≤((actualAllocations s.pools I).card:ℝ)^2*G/(rad*Dproj) := by
              calc
                _≤∑_B : actualAllocations s.pools I,((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
                  unfold cost geometryExceptionalMainNormRowMass
                  apply Finset.sum_le_sum
                  intro B _
                  split_ifs with hne
                  · exact hpoint B hne
                  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hG)
                      (mul_nonneg hrad.le hDproj.le)
                _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]; ring
            have hI0 : I≠0 := by
              dsimp only [I,geometryColumnIdeal]
              split_ifs <;> exact (by first | exact src.hD.1 | exact src.hC.1)
            have hIcap : (I.absNorm:ℝ)≤Z^(3:ℝ) := by
              dsimp only [I,geometryColumnIdeal]
              split_ifs
              · exact (actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 1).2
              · exact (actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 0).2
            have hcardalloc := hDa.2 (ι:=ι⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
              s.pools I hI0
            have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardalloc 2
            rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),
              show εalloc/2*(2:ℕ)=εalloc by norm_num] at hcard2
            have hcardZ : ((actualAllocations s.pools I).card:ℝ)^2≤Da^2*Z^(3*εalloc) := by
              apply hcard2.trans
              rw [Real.rpow_mul (zero_lt_one.trans hZ).le]
              exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hIcap hea.le) (sq_nonneg _)
            apply hrow.trans
            have hrpow : Z^(geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)=rad :=
              Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hrad
            have hpow : Z^(3*εalloc)*Pz*Rpow=Z^exponent := by
              dsimp only [Pz,Rpow,exponent,X]
              rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
              congr 1
              ring
            calc
              _≤(Da^2*Z^(3*εalloc))*G/(rad*Dproj) := by gcongr
              _=factor*Z^exponent/(rad*Dproj) := by
                dsimp only [factor,G]
                rw [←hpow]
                ring
              _=factor*Z^(exponent-geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)/Dproj := by
                rw [Real.rpow_sub (zero_lt_one.trans hZ),hrpow]
                ring
          have hfull := hz.2.2 s R seed (Z^M) hK bin hs hs0 hz₁ hz₂ hsourcepos hsource hV
            (by simpa only [Real.rpow_zero] using
              (inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le hM))) rows
            (fun j _=>actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
              (fun _=>logAnnulus) j (by assumption))
            (fun j _=>actual_geometry_projector_cap s N R seed (Z^M) Z ξ 3 hK hcard hZ.le
              (by norm_num) hpool bin j)
            factor exponent cost hfactor hc hcost
          have hpost (P : Finset (Ideal O)) (β loss Ccap : ℝ)
              (hbβ : 3401/100000≤β ∧ β≤1/25) (hCcap : 0≤Ccap)
              (hσ : sigma/3=GlobalNamed.amp β)
              (hprime : Z^(GlobalNamed.amp β-loss)≤(P.card:ℝ)) :
              (56/(P.card:ℝ))*((Ccap+6*GlobalNamed.amp β)/(GlobalNamed.amp β/2))*
                (∑j : rows,cost j)≤
              16800*(Ccap+1)*(Cd*factor*Z^(exponent+3*εcount-sigma/3)/(seed.absNorm:ℝ))*Z^loss := by
            let E := Cd*factor*Z^(exponent+3*εcount-sigma/3)/(seed.absNorm:ℝ)
            have hE : 0≤E := div_nonneg
              (mul_nonneg (mul_nonneg hCd.1.le hfactor) (Real.rpow_nonneg hZpos.le _))
              (Nat.cast_nonneg _)
            have hp : (0:ℝ)<P.card := (Real.rpow_pos_of_pos hZpos _).trans_le hprime
            have hamp : 0<GlobalNamed.amp β := GlobalNamed.amp_pos hbβ
            have hpref : 0≤(56/(P.card:ℝ))*
                ((Ccap+6*GlobalNamed.amp β)/(GlobalNamed.amp β/2)) :=
              mul_nonneg (div_nonneg (by norm_num) hp.le)
                (div_nonneg (add_nonneg hCcap (mul_nonneg (by norm_num) hamp.le))
                  (half_pos hamp).le)
            have hsplit : Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)=
                E*Z^(GlobalNamed.amp β) := by
              have hpow : Z^(exponent+3*εcount)=
                  Z^(exponent+3*εcount-sigma/3)*Z^(GlobalNamed.amp β) := by
                rw [←Real.rpow_add hZpos,←hσ]
                congr 1
                ring
              rw [hpow]
              dsimp only [E]
              ring
            calc
              _≤(56/(P.card:ℝ))*((Ccap+6*GlobalNamed.amp β)/(GlobalNamed.amp β/2))*
                  (Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)) :=
                mul_le_mul_of_nonneg_left hfull hpref
              _=_ := by rw [hsplit]
              _≤_ := Target836ErrorPayment.geometry_main_prime_payment P Z β loss Ccap E hZpos hbβ hCcap hE hprime
          exact And.intro hfull hpost))))))))


private theorem normalize_mass_mul (a b c : ℝ) : a/b*c=a*(c/b) := by ring

private theorem filtered_ray_norm_sum_le {T Ray : Type*} [Fintype T] [Fintype Ray]
    (selected : Finset T) (live : T→Prop) [DecidablePred live]
    (value : T→Ray→ℂ) (χ : selected→Ray) (w : T→ℂ) (c : T→ℝ)
    (hlive : ∀j∈selected,live j) (hc : ∀j,0≤c j) (hw : ∀j,‖w j‖≤c j) :
    (∑j : selected,‖w j.val*value j.val (χ j)‖)≤
      ∑ψ : Ray,∑j : T,if live j then c j*‖value j ψ‖ else 0 := by
  calc
    _≤∑j : selected,c j.val*(∑ψ : Ray,‖value j.val ψ‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw j.val) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (fun ψ _=>norm_nonneg (value j.val ψ)) (Finset.mem_univ (χ j))) (hc j.val))
    _=∑ψ : Ray,∑j : selected,c j.val*‖value j.val ψ‖ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _≤_ := by
      apply Finset.sum_le_sum
      intro ψ _
      rw [Finset.sum_coe_sort selected (fun j : T=>c j*‖value j ψ‖)]
      calc
        _=∑j∈selected,if live j then c j*‖value j ψ‖ else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ite_eq_left (hlive j hj)]
        _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _=>by split_ifs; exact mul_nonneg (hc j) (norm_nonneg _); exact le_rfl)

section MainRemainder
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ))
    (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
local notation "firsts" => GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ hK bin
local notation "allBlocks" => GeometryMainSecondIndex reflected s R seed Z M amp ξ reserve b t
    (Fintype.card ι) hZ bin
local notation "selected" => geometryMainNonzeroBlocks reflected s R seed Z M amp ξ reserve b t
    (Fintype.card ι) hZ bin hz₁ hz₂
local notation "phase" => (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ q))

/-- The exact original-full-block exceptional remainder from main contraction
is paid by positive source norm mass. A block-dependent ray costs one finite
ray sum; the physical second height coefficient has norm at most one. -/
theorem actual_geometry_main_exceptional_norm_remainder_le
    (χ : selected→RayCharacter) (Q : Ideal O) (m : O) :
    (∑j : selected,‖geometryMainSecondWeight reflected s R seed Z M amp ξ reserve b t
        (Fintype.card ι) hZ bin M (Real.logb Z (volume s)) phase j.val*
      (mainExceptionalDatum (geometryLowSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card ι) hZ bin j.val.1 hz₁ hz₂ j.val.2) (χ j) Q m).block.value ballProfile‖)≤
    ∑ψ : RayCharacter,∑j : firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
      (fun _=>logAnnulus),geometryExceptionalMainNormRowMass reflected s R seed Ψ ballProfile
        M Z ξ (3*amp) reserve t hZ (Fintype.card ι) b bin Q ψ m j.val := by
  let live := fun j : allBlocks=>frozenCoefficient j.1.2.val
    (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.1.1.val) R s.ν s.W s.P≠0
  let c := fun j : allBlocks=>geometryLowFirstWeight reflected s R seed (Z^M) Z ξ M
    (Real.logb Z (volume s)) hK bin phase b t j.1
  let value := fun (j : allBlocks) (ψ : RayCharacter)=>
    (mainExceptionalDatum (geometryLowSecondDatum reflected s R seed Z M amp ξ reserve b t
      (Fintype.card ι) hZ bin j.1 hz₁ hz₂ j.2) ψ Q m).block.value ballProfile
  have hc (j : allBlocks) : 0≤c j := geometry_low_first_weight_nonneg ..
  have hw (j : allBlocks) :
      ‖geometryMainSecondWeight reflected s R seed Z M amp ξ reserve b t
        (Fintype.card ι) hZ bin M (Real.logb Z (volume s)) phase j‖≤c j :=
    actual_main_block_weight_norm _ _ _ _ _ _ _ j.2 (c j) (hc j)
  have hh := filtered_ray_norm_sum_le selected live value χ
    (geometryMainSecondWeight reflected s R seed Z M amp ξ reserve b t
      (Fintype.card ι) hZ bin M (Real.logb Z (volume s)) phase) c
    (fun j hj=>(Finset.mem_filter.mp hj).2.1) hc hw
  apply hh.trans
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro ψ _
  rw [Fintype.sum_sigma]
  change (∑q : firsts,∑n : GeometryLowSecondIndex reflected s R seed Z M amp ξ reserve b t
      (Fintype.card ι) hZ bin q,if live ⟨q,n⟩ then c ⟨q,n⟩*‖value ⟨q,n⟩ ψ‖ else 0)=_
  have hsource (q : firsts) :
      (∑n : GeometryLowSecondIndex reflected s R seed Z M amp ξ reserve b t
        (Fintype.card ι) hZ bin q,‖value ⟨q,n⟩ ψ‖)=
      exceptionalPhysicalNormSum
        (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK bin t q).η ψ Q m t
        (finiteColumns (Fintype.piFinset
          (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK bin t q).pools))
        (coefficient (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK bin t q)
          (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val) q.1.val.2.1.val)
        ballProfile
        (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*amp) reserve
          (geometryFirstLabel s R seed (Z^M) Z ξ hK bin q.1.val))
        (firstMainFourierScale reflected (Z^M) (volume s) Z ξ (3*amp) reserve b (Fintype.card ι)
          (geometryFirstLabel s R seed (Z^M) Z ξ hK bin q.1.val)) Z ξ
        (sourceRadius (geometryLowFirstChild reflected s R seed (Z^M) Z ξ hK bin t q)) :=
    actual_original_exceptional_norm_assembly (liveIndices q.2.val) _ _ _
      (actual_first_live_squarefree _ (fun _=>logAnnulus) q.1.val q.1.property)
      hz₁ hz₂ ψ Q m ballProfile _ _ Z ξ
      (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*amp) reserve
        (zero_lt_one.trans hZ) _)
  calc
    _=∑q : firsts,if frozenCoefficient q.2.val
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val) R s.ν s.W s.P≠0
      then geometryLowFirstWeight reflected s R seed (Z^M) Z ξ M
        (Real.logb Z (volume s)) hK bin phase b t q*(∑n,‖value ⟨q,n⟩ ψ‖) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      dsimp only [live,c]
      split_ifs <;> simp only [Finset.mul_sum,Finset.sum_const_zero]
    _=_ := by
      simp_rw [hsource]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      unfold geometryExceptionalMainNormRowMass
      apply Finset.sum_congr rfl
      intro B _
      dsimp only [live,geometryLowFirstWeight,geometryLowFirstChild]
      split_ifs
      · exact normalize_mass_mul _ _ _
      · rfl
end MainRemainder


private theorem sum_uniform_bound {A : Type*} [Fintype A] (f : A→ℝ)
    (U : ℝ) (h : ∀a,f a≤U) : (∑a,f a)≤(Fintype.card A:ℝ)*U := by
  calc
    _≤∑_a : A,U := Finset.sum_le_sum (fun a _=>h a)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

attribute [local irreducible] geometryMainNonzeroBlocks geometryMainSecondWeight geometryLowSecondDatum

set_option linter.defProp false in
/-- Complete actual main exceptional payment, consuming the original-full-zero
filtered physical-block remainder with block-dependent inducing rays. The saved
profile and norm-source constants precede every moving family. The only ray fee
is its fixed finite cardinality; the prime average cancels amplification once. -/
def actual_geometry_main_exceptional_norm_payment
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (ε δ θ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0< slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1) :=
  let full := actual_geometry_main_exceptional_norm_full wlo whi hwlo hwhi lo hi ballProfile
    ε δ θ hε hδ hθ η (Fintype.card ι) b bs hb hbs
    slotlo εalloc εcount ξ hslot hea hec hξ hξ₁
  let J := full.1
  let Sp := full.2.1
  let Ck := full.2.2.1
  (J,Sp,Ck,fun (Qfix : Ideal O) hQ hQt hQ72=>
    let saved := full.2.2.2 Qfix hQ hQt hQ72
    let Kfix := saved.1
    let Cd := saved.2.1
    let Da := saved.2.2.1
    (Kfix,Cd,Da,PLift.up
      (And.intro saved.2.2.2.down.1 (And.intro saved.2.2.2.down.2.1
        (And.intro saved.2.2.2.down.2.2.1
          (Filter.Eventually.mono saved.2.2.2.down.2.2.2 (fun Z hz=>
            And.intro hz.1
              (fun (hZ : 1<Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
                (hend : Endpoints b bs bs s) (hlower : slotlo≤ s.lower) (hsP : ∀i,1≤ s.P i)
                (p : Profiles wlo whi) (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
                (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed) (hs0 : seed≠0)
                (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
                (hV : volume s≤Z^(2:ℝ)) (hsourcepos : 0< sourceRadius s)
                (hsource : sourceRadius s≤Z^(3:ℝ))
                (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^(3:ℝ))
                (hRN : (R.absNorm:ℝ)≤Z) (M amp reserve t plainLoss : ℝ)
                (hM : 0≤M) (hKM : Z^M≤Z) (hamp : 0≤amp) (hreserve : 0≤reserve)
                (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
                (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
                (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
                (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂)
                (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
                (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
                (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (bin : ℤ×(Fin 5→ℤ))
                (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
                fun (χ : geometryMainNonzeroBlocks reflected s R seed Z M amp ξ reserve b t
                  (Fintype.card ι) hZ bin hz₁ hz₂→RayCharacter)=>
                  let hraw := fun ψ=>hz.2 hZ s hlo hhi hη le_rfl hend hlower hsP p hW₁ hW₂
                    R seed hR hs hs0 hz₁ hz₂ hV hsourcepos hsource hpool hRN M (3*amp)
                    reserve t plainLoss hM hKM (mul_nonneg (by norm_num) hamp) hreserve
                    hX₁ hX₂ hY₁ hY₂ a₁ a₂ ha₁ ha₂ hs₁ hs₂ reflected Ψ bin ψ m hm hml hm2
                  let cost := fun ψ=>∑j : firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ
                    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin) (fun _=>logAnnulus),
                    geometryExceptionalMainNormRowMass reflected s R seed Ψ ballProfile M Z ξ
                      (3*amp) reserve t hZ (Fintype.card ι) b bin Qfix ψ m j.val
                  let Hshell := Z^((bin.2 1:ℝ)*Real.logb Z 2)
                  let Control := p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6
                  let Shell := if reflected then 1/Hshell
                    else (4/((∏i,s.lo i)*a₁*a₂))^2*(2*Hshell)
                  let coef := max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
                    (Fintype.card ι) b J Qfix Kfix)
                  let factor := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^(Fintype.card ι)*
                    coef*geometryExceptionalLowerConstant (Fintype.card ι) slotlo wlo*Control*
                    (b^(Fintype.card ι))^(1/3:ℝ)*Da^2
                  let exponent := 2*ε+2*δ+2*41*θ+(3*amp)/3+
                    Real.logb Z (geometryExceptionalVolume s)-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
                    4*(3*amp)/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3+3*εalloc
                  let E := Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)
                  have hselected := actual_geometry_main_exceptional_norm_remainder_le reflected s R seed Ψ
                    Z M amp ξ reserve b t hZ bin hz₁ hz₂ χ Qfix m
                  have hsum : (∑ψ : RayCharacter,cost ψ)≤(Fintype.card RayCharacter:ℝ)*E :=
                    sum_uniform_bound cost E (fun ψ=>(hraw ψ).1)
                  have hpaid := hselected.trans hsum
                  let hpostBound := fun (P : Finset (Ideal O)) (β loss Ccap : ℝ)
                      (hbβ : 3401/100000≤β ∧ β≤1/25) (hCcap : 0≤Ccap)
                      (hσ : (3*amp)/3=GlobalNamed.amp β)
                      (hprime : Z^(GlobalNamed.amp β-loss)≤(P.card:ℝ))=>
                    have hp : (0:ℝ)<P.card := (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).trans_le hprime
                    have ha := GlobalNamed.amp_pos hbβ
                    let pref := (56/(P.card:ℝ))*
                      ((Ccap+6*GlobalNamed.amp β)/(GlobalNamed.amp β/2))
                    have hpref : 0≤pref := mul_nonneg (div_nonneg (by norm_num) hp.le)
                      (div_nonneg (add_nonneg hCcap (mul_nonneg (by norm_num) ha.le)) (half_pos ha).le)
                    let Epost := 16800*(Ccap+1)*(Cd*factor*Z^(exponent+3*εcount-(3*amp)/3)/
                      (seed.absNorm:ℝ))*Z^loss
                    have hpost : (∑ψ : RayCharacter,pref*cost ψ)≤
                        (Fintype.card RayCharacter:ℝ)*Epost :=
                      sum_uniform_bound (fun ψ=>pref*cost ψ) Epost
                        (fun ψ=>(hraw ψ).2 P β loss Ccap hbβ hCcap hσ hprime)
                    have hpost' : pref*(∑ψ : RayCharacter,cost ψ)≤
                        (Fintype.card RayCharacter:ℝ)*Epost := by
                      simpa only [Finset.mul_sum] using hpost
                    (mul_le_mul_of_nonneg_left hselected hpref).trans hpost' 
                  And.intro hpaid hpostBound))))))))

end
end OAI.SevenEighths.Target836SourceAssembly

#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_geometry_main_exceptional_norm_paid

#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_geometry_error_exceptional_norm_paid

#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_geometry_main_exceptional_norm_closed

#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_geometry_error_exceptional_norm_closed

#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_geometry_main_exceptional_norm_full

#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_geometry_main_exceptional_norm_remainder_le

#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_geometry_main_exceptional_norm_payment
