/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B063
import Submissions.gao_cycle61_plane_20261013.Bundles.B108
import Submissions.gao_cycle61_plane_20261013.Bundles.B138
import Submissions.gao_cycle61_plane_20261013.Bundles.B139
import Submissions.gao_cycle61_plane_20261013.Bundles.B140
import Submissions.gao_cycle61_plane_20261013.Bundles.B155
import Submissions.gao_cycle61_plane_20261013.Bundles.B158

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalNormPayment; sha256 cdc41cbc8f21d700744206b075822542a4197f764a994bcfd527ba91d81b58fb -/
section
                                                                  
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Cycle61Moment HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
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
    0≤ exceptionalPhysicalNormSum η χ Q m t S β W K Tsec Z ξ H := by
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
variable (M Z ξ sigma reserve t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
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
    (hKfix : 0≤ Kfix) (hCk : 0≤ Ck)
    (N : ℕ) (b : ℝ) (hb : 1≤ b) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
    :=
    let I := (geometryColumnIdeal reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
    let τ := (geometryColumnCharacter reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
    let u := child s I R B τ t
    let src := (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1)
    let Kmain := (firstMainRadius reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve (geometryFirstLabel s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
    fun (hest : geometryExceptionalNormSourceEstimate wlo whi u.lo u.hi W ε δ θ Bcap L Cr
      J Sp Ck Qfix Kfix Z)
    (hP : ∀i,1≤ u.P i) (hp₁ : u.W₁=p.profile 0) (hp₂ : u.W₂=p.profile 1)
    (hR : R*I≠0) (hseed : Squarefree j.2.1.val) (hseed0 : j.2.1.val≠0)
    (hcap : sourceRadius u≤ Z^Bcap) (χ₀ : RayCharacter) (m : O)
    (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Tsec : ℝ)
    (hF : 0< frequencyRadius Tsec Z ξ) (hFc : frequencyRadius Tsec Z ξ≤ Cr*Z^L)
    (hcond : (expandedFactor u.η:ℝ)*(R*I).absNorm*(sourceRadius u)^2*
      (4*frequencyRadius Tsec Z ξ)≤ Z^Bcap)
    (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0)=>
    have hparentV : 0< geometryExceptionalVolume s :=
      CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
    have hchildV : 0< geometryExceptionalVolume u :=
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
    have hbn : 0≤ b^N := pow_nonneg (zero_le_one.trans hb) _
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
    have hzero : 0≤ exceptionalPhysicalNormSum u.η χ₀ Qfix m u.t
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
    have hU : 0≤ U := by
      dsimp only [U]
      exact mul_nonneg (mul_nonneg hside
        (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le))
        (div_nonneg (div_nonneg hparentV.le hI.le)
          (mul_nonneg (mul_nonneg hτ.le (sq_nonneg _))
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
    have hA : 0≤ A :=
      mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _)
        (Nat.cast_nonneg _)
    have hD : 0≤ Dpaid := by
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
    have hPf : 0≤ Pf := profileFactor_nonneg Sp u p J Qfix Kfix hKfix
    have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (geometryExceptionalVolume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
      (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ q)) N b j B≤ U*A*F := by
      convert hw using 1 <;> dsimp only [U,A,F,geometryExceptionalVolume] <;> ring
    have hpower : Z^(2*ε+2*δ+2*Bcap*θ-2*max (inputCap Z u) 0/3)=
      Z^(2*ε+2*δ+2*Bcap*θ+sigma/3)*Z^(-sigma/3)*Z^(-2*max (inputCap Z u) 0/3) := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 1
      ring
    have he0 : E≤ Dpaid*Pf*Vc := by
      have hh := he
      conv_rhs at hh => arg 1;arg 1;arg 1;arg 1;arg 2;rw [hpower]
      convert hh using 1 <;> dsimp only [E,Dpaid,Pf,Vc,geometryExceptionalVolume] <;> ring
    have hp0 : F*Pf≤ Ppaid := hp
    have hv0 : Vc≤ Vb := hvol
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
    (hKfix : 0≤ Kfix) (hCk : 0≤ Ck)
    (N : ℕ) (b : ℝ) (hb : 1≤ b) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N)
    (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x) :=
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
      (hP : ∀i,1≤ u.P i) (hp₁ : u.W₁=p0.profile 0) (hp₂ : u.W₂=p0.profile 1)
      (hR : (R*I)*(Q^k)≠0) (hseed : Squarefree j.2.1.val) (hseed0 : j.2.1.val≠0)
      (hcap : sourceRadius u≤ Z^Bcap) (χ₀ : RayCharacter) (m : O)
      (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Tsec : ℝ)
      (hF : 0< frequencyRadius Tsec Z ξ) (hFc : frequencyRadius Tsec Z ξ≤ Cr*Z^L)
      (hcond : (expandedFactor u.η:ℝ)*((R*I)*(Q^k)).absNorm*(sourceRadius u)^2*
        (4*frequencyRadius Tsec Z ξ)≤ Z^Bcap)
      (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0) =>
    have hparentV : 0< geometryExceptionalVolume s :=
      CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
    have hchildV : 0< geometryExceptionalVolume u :=
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
    have hbn : 0≤ b^N := pow_nonneg (zero_le_one.trans hb) _
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
        profileFactor Sp u p0 J Qfix Kfix≤ _ at hh
      rw [hfBp,one_pow,mul_one] at hh
      exact hh
    have hv1 := common_volume_le N b hb s hc hu I R B τ t hne
    have hv : geometryExceptionalVolume u≤ b^N*geometryExceptionalVolume s/(I.absNorm:ℝ)/(Q.absNorm:ℝ)^k := by
      change CenteredMomentAmplificationChildInput.volume (twiceChild s I R B τ t Q k Bp υ v)≤ _
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
    have hzero : 0≤ exceptionalPhysicalNormSum u.η χ₀ Qfix m u.t
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
    have hU : 0≤ U := by
      dsimp only [U]
      exact mul_nonneg (mul_nonneg hside
        (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le))
        (div_nonneg (div_nonneg hparentV.le hI.le)
          (mul_nonneg (mul_nonneg hτ.le (sq_nonneg _))
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
    have hA : 0≤ A :=
      mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _)
        (Nat.cast_nonneg _)
    have hD : 0≤ Dpaid := by
      dsimp only [Dpaid]
      exact div_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg hCk (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
        (Real.rpow_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) _)) hlower)
        (Nat.cast_nonneg _)
    have hPf : 0≤ Pf := profileFactor_nonneg Sp u p0 J Qfix Kfix hKfix
    have hw0 : geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (geometryExceptionalVolume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
      (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ q)) N b j B≤ U*A*F := by
      convert hw using 1 <;> dsimp only [U,A,F,geometryExceptionalVolume] <;> ring
    have he0 : E≤ Dpaid*Pf*Vc := by
      convert he using 1 <;> dsimp only [E,Dpaid,Pf,Vc,geometryExceptionalVolume] <;> ring
    have hp0 : F*Pf≤ Ppaid := hp'
    have hv0 : Vc≤ Vb := hvol
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
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs) :=
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
          (fun (hZ : 1< Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤ N) (hend : Endpoints b bs bs s)
            (hsP : ∀i,1≤ s.P i) (p : Profiles wlo whi)
            (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤ Z^(2:ℝ)) (hsource : sourceRadius s≤ Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤ Z) (M ξ sigma reserve t : ℝ)
            (hKM : Z^M≤ Z) (hξ : 0≤ξ) (hξ₁ : ξ≤1)
            (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
            (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
            (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
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
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs) :=
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
          let hpayed := (fun (hZ : 1< Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤ N) (hend : Endpoints b bs bs s)
            (hsP : ∀i,1≤ s.P i) (p0 : Profiles wlo whi)
            (hW₁ : s.W₁=p0.profile 0) (hW₂ : s.W₂=p0.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤ Z^(2:ℝ)) (hsource : sourceRadius s≤ Z^(3:ℝ))
            (hlogV : |Real.logb Z (volume s)|≤3) (hRN : (R.absNorm:ℝ)≤ Z)
            (amp ξ reserve t : ℝ) (ha : 0≤ amp) (ha₁ : amp≤1)
            (hξ : 0≤ξ) (hξ₁ : ξ≤1) (hreserve : 0≤ reserve)
            (hω : frequencyLoss Z 32 ξ+reserve≤3)
            (a₁ a₂ : ℝ) (ha₁p : 0< a₁) (ha₂p : 0< a₂)
            (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
            (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (bin : ℤ×(Fin 5→ℤ))=>
          let hKMpos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
          fun (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin)
            (hne : frozenCoefficient q.2.val
              (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val)
              R s.ν s.W s.P≠0) (p : O) (hp : p≠0)
            (hpN : ((Ideal.span {p}).absNorm:ℝ)≤ Z^(3:ℝ))
            (hslot : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
              hKMpos bin t q).slots j→ IsCoprime (Ideal.span {p}) I) (i : Fin 3)
            (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
              (Z^(1:ℝ)) Z ξ hKMpos bin t q)).pools ((Ideal.span {p})^(errorIndex i+1)))
            (υ : Character) (χ : RayCharacter) (v : ℝ)
            (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter
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
    (Ψ W : 𝓢(ℝ,ℂ)) (M Z ξ sigma reserve t : ℝ) (hZ : 1< Z)
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
    (hpaid : E≤ S*F*q*A*(Ck*Pz*mr*kr*lower/D)*(Cprof*Control*bro*volumeRoot))
    (hside : S≤ Shell) (hlower : lower≤ L) (href : q*volumeRoot*kr*mr≤ Rpow)
    (hS : 0≤ S) (hShell : 0≤ Shell) (hF : 0≤ F) (hA : 0≤ A)
    (hP : 0≤ Pz) (hl : 0≤ lower) (hL : 0≤ L) (hD : 0≤ D)
    (hc : 0≤ Control) (hb : 0≤ bro) (hq : 0≤ q) (hi : 0≤ volumeRoot)
    (hk : 0≤ kr) (hm : 0≤ mr) :
    E≤ Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*Control*bro*Rpow := by
  let rest := S*F*A*Pz*(lower/D)*Control*bro*(q*volumeRoot*kr*mr)
  have hrest : 0≤ rest := by dsimp only [rest]; positivity
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
    (hside : S≤ Shell) (hlower : lower≤ L) (href : q*root*kr*m₁*m₂≤ Rpow)
    (hS : 0≤ S) (hShell : 0≤ Shell) (hF : 0≤ F) (hA : 0≤ A)
    (hP : 0≤ Pz) (hl : 0≤ lower) (hL : 0≤ L) (hD : 0≤ D)
    (hc : 0≤ c*height*mass) (hb : 0≤ bro) (hq : 0≤ q) (hi : 0≤ root)
    (hk : 0≤ kr) (hm : 0≤ m₁*m₂) :
    E≤ Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*(c*height*mass)*bro*Rpow := by
  exact full_main_fold_algebra E S Shell F A Ck Cprof Pz lower L D
    (c*height*mass) bro q root kr (m₁*m₂) Rpow
    (by convert hpaid using 1; ring) hside hlower
    (by convert href using 1; ring) hS hShell hF hA hP hl hL hD hc hb hq hi hk hm

set_option linter.defProp false in
/-- The complete supported main family derives its allocation costs from
the saved exceptional physical-block norm estimate. The original projector and radical
are paid jointly before all four dyads and both rays are counted. -/
def actual_geometry_main_exceptional_norm_full
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs)
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
          (fun (hZ : 1< Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤ N) (hend : Endpoints b bs bs s)
            (hlower : slotlo≤ s.lower) (hsP : ∀i,1≤ s.P i)
            (p : Profiles wlo whi) (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed) (hs0 : seed≠0)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤ Z^(2:ℝ)) (hsourcepos : 0< sourceRadius s)
            (hsource : sourceRadius s≤ Z^(3:ℝ))
            (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤ Z) (M sigma reserve t plainLoss : ℝ)
            (hM : 0≤ M) (hKM : Z^M≤ Z) (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
            (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
            (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
            (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
            (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂)
            (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
            (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
            (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (bin : ℤ×(Fin 5→ℤ))
            (χ₀ : RayCharacter) (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
          let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
          let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
            (fun _=>logAnnulus)
          by
          have hZpos : 0< Z := zero_lt_one.trans hZ
          let Hshell := Z^((bin.2 1:ℝ)*Real.logb Z 2)
          have hH : 0< Hshell := Real.rpow_pos_of_pos hZpos _
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
          have hfixed : 0< fixedPresentationCost := fixedPresentationCost_pos
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
          have hShell : 0≤ Shell := by dsimp only [Shell]; split_ifs <;> positivity
          have hLower : 0≤ geometryExceptionalLowerConstant N slotlo wlo :=
            Real.rpow_nonneg (by positivity) _
          have hControl : 0≤ Control := by dsimp only [Control]; positivity
          have hfactor : 0≤ factor := by dsimp only [factor,coef]; positivity
          have hc : ∀j : rows,0≤ cost j := by
            intro j
            unfold cost geometryExceptionalMainNormRowMass
            apply Finset.sum_nonneg
            intro B _
            split_ifs
            · exact mul_nonneg (geometryAllocationWeight_nonneg ..)
                (div_nonneg (exceptional_norm_mass_nonneg ..) (CenteredMomentExceptionalAmplitudePair.volume_pos _).le)
            · exact le_rfl
          have hcost : ∀j : rows,cost j≤ factor*
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
            have hG : 0≤ G := by dsimp only [G,coef,Pz,Rpow]; positivity
            have hrad : 0< rad := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero _ _)
            have hDproj : 0< Dproj := CenteredMomentFirstScale.norm_pos _
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
              have hXpos : 0< X := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
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
              have hside : side≤ Shell := by
                dsimp only [side,Shell]
                split_ifs
                · exact div_le_div_of_nonneg_left zero_le_one hH (hphysical j).1
                · exact mul_le_mul_of_nonneg_left (hphysical j).2 (sq_nonneg _)
              have hqfac : 0≤ qfac := by dsimp only [qfac,den]; positivity
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
            have hIcap : (I.absNorm:ℝ)≤ Z^(3:ℝ) := by
              dsimp only [I,geometryColumnIdeal]
              split_ifs
              · exact (actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 1).2
              · exact (actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 0).2
            have hcardalloc := hDa.2 (ι:=ι⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
              s.pools I hI0
            have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardalloc 2
            rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),
              show εalloc/2*(2:ℕ)=εalloc by norm_num] at hcard2
            have hcardZ : ((actualAllocations s.pools I).card:ℝ)^2≤ Da^2*Z^(3*εalloc) := by
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
              (hbβ : 3401/100000≤β ∧ β≤1/25) (hCcap : 0≤ Ccap)
              (hσ : sigma/3=Cycle61.Arithmetic.amp β)
              (hprime : Z^(Cycle61.Arithmetic.amp β-loss)≤(P.card:ℝ)) :
              (56/(P.card:ℝ))*((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2))*
                (∑j : rows,cost j)≤
              22400*(Ccap+1)*(Cd*factor*Z^(exponent+3*εcount-sigma/3)/(seed.absNorm:ℝ))*Z^loss := by
            let E := Cd*factor*Z^(exponent+3*εcount-sigma/3)/(seed.absNorm:ℝ)
            have hE : 0≤ E := div_nonneg
              (mul_nonneg (mul_nonneg hCd.1.le hfactor) (Real.rpow_nonneg hZpos.le _))
              (Nat.cast_nonneg _)
            have hp : (0:ℝ)< P.card := (Real.rpow_pos_of_pos hZpos _).trans_le hprime
            have hamp : 0< Cycle61.Arithmetic.amp β := Cycle61.Arithmetic.amp_pos hbβ
            have hpref : 0≤(56/(P.card:ℝ))*
                ((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2)) :=
              mul_nonneg (div_nonneg (by norm_num) hp.le)
                (div_nonneg (add_nonneg hCcap (mul_nonneg (by norm_num) hamp.le))
                  (half_pos hamp).le)
            have hsplit : Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)=
                E*Z^(Cycle61.Arithmetic.amp β) := by
              have hpow : Z^(exponent+3*εcount)=
                  Z^(exponent+3*εcount-sigma/3)*Z^(Cycle61.Arithmetic.amp β) := by
                rw [←Real.rpow_add hZpos,←hσ]
                congr 1
                ring
              rw [hpow]
              dsimp only [E]
              ring
            calc
              _≤(56/(P.card:ℝ))*((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2))*
                  (Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)) :=
                mul_le_mul_of_nonneg_left hfull hpref
              _=_ := by rw [hsplit]
              _≤ _ := geometry_main_prime_payment P Z β loss Ccap E hZpos hbβ hCcap hE hprime
          exact And.intro hfull hpost))))))))


private theorem normalize_mass_mul (a b c : ℝ) : a/b*c=a*(c/b) := by ring

private theorem filtered_ray_norm_sum_le {T Ray : Type*} [Fintype T] [Fintype Ray]
    (selected : Finset T) (live : T→ Prop) [DecidablePred live]
    (value : T→ Ray→ℂ) (χ : selected→ Ray) (w : T→ℂ) (c : T→ℝ)
    (hlive : ∀j∈selected,live j) (hc : ∀j,0≤ c j) (hw : ∀j,‖w j‖≤ c j) :
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
    _≤ _ := by
      apply Finset.sum_le_sum
      intro ψ _
      rw [Finset.sum_coe_sort selected (fun j : T=>c j*‖value j ψ‖)]
      calc
        _=∑j∈selected,if live j then c j*‖value j ψ‖ else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ite_eq_left (hlive j hj)]
        _≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _=>by split_ifs; exact mul_nonneg (hc j) (norm_nonneg _); exact le_rfl)

section MainRemainder
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ))
    (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
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
    (χ : selected→ RayCharacter) (Q : Ideal O) (m : O) :
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
  have hc (j : allBlocks) : 0≤ c j := geometry_low_first_weight_nonneg ..
  have hw (j : allBlocks) :
      ‖geometryMainSecondWeight reflected s R seed Z M amp ξ reserve b t
        (Fintype.card ι) hZ bin M (Real.logb Z (volume s)) phase j‖≤ c j :=
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
    (U : ℝ) (h : ∀a,f a≤ U) : (∑a,f a)≤(Fintype.card A:ℝ)*U := by
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
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (ε δ θ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs)
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
              (fun (hZ : 1< Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
                (hend : Endpoints b bs bs s) (hlower : slotlo≤ s.lower) (hsP : ∀i,1≤ s.P i)
                (p : Profiles wlo whi) (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
                (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed) (hs0 : seed≠0)
                (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
                (hV : volume s≤ Z^(2:ℝ)) (hsourcepos : 0< sourceRadius s)
                (hsource : sourceRadius s≤ Z^(3:ℝ))
                (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^(3:ℝ))
                (hRN : (R.absNorm:ℝ)≤ Z) (M amp reserve t plainLoss : ℝ)
                (hM : 0≤ M) (hKM : Z^M≤ Z) (hamp : 0≤ amp) (hreserve : 0≤ reserve)
                (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
                (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
                (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
                (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂)
                (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
                (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
                (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (bin : ℤ×(Fin 5→ℤ))
                (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
                fun (χ : geometryMainNonzeroBlocks reflected s R seed Z M amp ξ reserve b t
                  (Fintype.card ι) hZ bin hz₁ hz₂→ RayCharacter)=>
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
                      (hbβ : 3401/100000≤β ∧ β≤1/25) (hCcap : 0≤ Ccap)
                      (hσ : (3*amp)/3=Cycle61.Arithmetic.amp β)
                      (hprime : Z^(Cycle61.Arithmetic.amp β-loss)≤(P.card:ℝ))=>
                    have hp : (0:ℝ)< P.card := (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).trans_le hprime
                    have ha := Cycle61.Arithmetic.amp_pos hbβ
                    let pref := (56/(P.card:ℝ))*
                      ((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2))
                    have hpref : 0≤ pref := mul_nonneg (div_nonneg (by norm_num) hp.le)
                      (div_nonneg (add_nonneg hCcap (mul_nonneg (by norm_num) ha.le)) (half_pos ha).le)
                    let Epost := 22400*(Ccap+1)*(Cd*factor*Z^(exponent+3*εcount-(3*amp)/3)/
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
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_norm_paid

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_norm_paid

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_norm_closed

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_norm_closed

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_norm_full

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_norm_remainder_le

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_norm_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalNormPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalErrorNormPayment; sha256 04bdec5ac5aa0b1f18b0b2326e943ca5af9e3fe6c1ad86beba77c4a0315c3259 -/
section
                                                                  
                                                           

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Cycle61Moment HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
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
local instance exceptionalErrorNormPaymentSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _


open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentFirstPhysicalSource

section Selected
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ))
    (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key)
    (P : Finset (Ideal O)) (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key t q)).pools
        ((Ideal.span {p})^(errorIndex i+1)))
    (υ : Character) (v : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "selected" => geometryErrorNonzeroBlocks reflected s R seed Z M amp ξ reserve b t
    (Fintype.card ι) hZ key q p i Bp υ v hz₁ hz₂

set_option linter.defProp false in
/-- The literal extracted coefficient pays the original-full-zero-filtered
exceptional block norm sum. The factor 56/P is included once; inducing rays
may vary by block, and the actual second height coefficient costs at most one. -/
def actual_geometry_error_exceptional_selected_norm_le
    (χ : selected→ RayCharacter) (Q : Ideal O) (m : O) :=
  let src := geometryErrorChild reflected s R seed Z M ξ t hZ key q p i Bp υ v
  let slots := liveIndices (errorActiveAllocation
    (geometryLowFirstChild reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key t q) _ Bp).val
  let R₂ := (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key q.1.val)*
    (Ideal.span {p})^(errorIndex i+1)
  let K₂ := geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ key q p i
  let T₂ := geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b
    (Fintype.card ι) hZ key q p i
  let weight := geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
    (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key
    (fun c=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ c))
    (Fintype.card ι) b q.1.val q.2
  let c := errorNormalizedCoefficient P weight (volume src) p i
  have hc : 0≤ c := error_normalized_coefficient_nonneg P weight (volume src)
    (geometryAllocationWeight_nonneg ..)
    (CenteredMomentAmplificationChildInput.volume_pos src) p i
  actual_filtered_exceptional_weighted_ray_sum_le slots src R₂ q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key)
      (fun _=>logAnnulus) q.1.val q.1.property) hz₁ hz₂ Q m ballProfile K₂ T₂ Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ key q p i)
    χ (fun n=>(c:ℂ)*actualSecondBlockWeight src R₂ q.1.val.2.1.val K₂ T₂ Z ξ n.val)
    c hc (fun n=>actual_error_block_weight_norm src R₂ q.1.val.2.1.val K₂ T₂ Z ξ n.val c hc)


/-- Genuine normalized exceptional source mass for one fixed extracted
allocation. Both physical menus are fixed before any second row is summed. -/
def geometryExceptionalErrorNormSourceMass (Q : Ideal O) (m : O)
    (χ₀ : RayCharacter) : ℝ :=
  let src := geometryErrorChild reflected s R seed Z M ξ t hZ key q p i Bp υ v
  errorNormalizedCoefficient P
    (geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key
      (fun c=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ c))
      (Fintype.card ι) b q.1.val q.2) (volume src) p i*
    exceptionalPhysicalNormSum src.η χ₀ Q m src.t
      (finiteColumns (Fintype.piFinset src.pools))
      (coefficient src ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key q.1.val)*
        (Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val) ballProfile
      (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ key q p i)
      (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card ι)
        hZ key q p i) Z ξ (sourceRadius src)

omit [DecidableEq ι] in
private theorem active_error_allocation_card (hp : Prime (Ideal.span {p}))
    (hslot : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key t q).slots j→
        IsCoprime (Ideal.span {p}) I) :
    (actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))).card≤8 := by
  apply CenteredMomentAmplificationAllocationCost.actual_error_allocations_card _ _ hp _
  · fin_cases i <;> norm_num [errorIndex]
  · intro j I hI
    exact ⟨((activeInput _).prime j I hI).ne_zero,
      hslot j I (Finset.mem_filter.mp hI).1⟩

private theorem error_index_price_cap : (16*(errorIndex i+2:ℝ))≤128 := by
  fin_cases i <;> norm_num [errorIndex]

end Selected


open CenteredMomentPrimeElements CenteredMomentAmplificationAllocationCost

private theorem error_menu_count_le {α : Type*} [Fintype α]
    (u : Input α) (P : Finset (Ideal O))
    (hprime : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hslot : ∀p∈elementPool P,∀j I,I∈u.slots j→ IsCoprime (Ideal.span {p}) I)
    (f : (p : elementPool P)→(i : Fin 3)→ RayCharacter→
      actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1))→
      RayCharacter→ℝ) (U : ℝ) (hU : 0≤ U)
    (hf : ∀p i ψ Bp χ,f p i ψ Bp χ≤ U) :
    (∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
      ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        ∑χ : RayCharacter,f p i ψ Bp χ)≤
      (P.card:ℝ)*3*(Fintype.card RayCharacter:ℝ)*8*(Fintype.card RayCharacter:ℝ)*U := by
  have hcard (p : elementPool P) (i : Fin 3) :
      (actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1))).card≤8 := by
    have hp : Prime (Ideal.span {p.val}) := hprime _ (elementPool_data P hprime hbad p.val p.property).2.1
    apply actual_error_allocations_card _ _ hp _
    · fin_cases i <;> norm_num [errorIndex]
    · intro j I hI
      exact ⟨((activeInput u).prime j I hI).ne_zero,
        hslot p.val p.property j I (Finset.mem_filter.mp hI).1⟩
  calc
    _≤∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
        ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1)),
          ∑χ : RayCharacter,U := by
      apply Finset.sum_le_sum; intro p _
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro ψ _
      apply Finset.sum_le_sum; intro Bp _
      apply Finset.sum_le_sum; intro χ _
      exact hf p i ψ Bp χ
    _≤∑_p : elementPool P,∑_i : Fin 3,∑_ψ : RayCharacter,
        8*((Fintype.card RayCharacter:ℝ)*U) := by
      apply Finset.sum_le_sum; intro p _
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro ψ _
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard p i))
        (mul_nonneg (Nat.cast_nonneg _) hU)
    _=_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,
        Fintype.card_fin,nsmul_eq_mul,elementPool_card P hprime hbad]
      ring

private theorem prime_average_count_le (P : Finset (Ideal O)) :
    (P.card:ℝ)*(56/(P.card:ℝ))≤56 := by
  by_cases h : P.card=0
  · simp only [h,Nat.cast_zero,div_zero,mul_zero]; norm_num
  · have hp : (P.card:ℝ)≠0 := Nat.cast_ne_zero.mpr h
    exact le_of_eq (by field_simp)

private theorem error_menu_average_le {α : Type*} [Fintype α]
    (u : Input α) (P : Finset (Ideal O))
    (hprime : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hslot : ∀p∈elementPool P,∀j I,I∈u.slots j→ IsCoprime (Ideal.span {p}) I)
    (f : (p : elementPool P)→(i : Fin 3)→ RayCharacter→
      actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1))→
      RayCharacter→ℝ) (E : ℝ) (hE : 0≤ E)
    (hf : ∀p i ψ Bp χ,f p i ψ Bp χ≤(56/(P.card:ℝ))*128*E) :
    (∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
      ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        ∑χ : RayCharacter,f p i ψ Bp χ)≤
      56*128*3*8*(Fintype.card RayCharacter:ℝ)^2*E := by
  have hU : 0≤(56/(P.card:ℝ))*128*E := by positivity
  have hh := error_menu_count_le u P hprime hbad hslot f _ hU hf
  calc
    _≤ _ := hh
    _=(P.card:ℝ)*(56/(P.card:ℝ))*(128*3*8*(Fintype.card RayCharacter:ℝ)^2*E) := by ring
    _≤56*(128*3*8*(Fintype.card RayCharacter:ℝ)^2*E) :=
      mul_le_mul_of_nonneg_right (prime_average_count_le P) (by positivity)
    _=_ := by ring

private theorem error_norm_fold_algebra
    (E S Shell F A Ck Cprof Pz lower L D Control bro q volumeRoot kr mr Rpow : ℝ)
    (hpaid : E≤ S*F*q*A*(Ck*Pz*mr*kr*lower/D)*(Cprof*Control*bro*volumeRoot))
    (hside : S≤ Shell) (hlower : lower≤ L) (href : q*volumeRoot*kr*mr≤ Rpow)
    (hS : 0≤ S) (hShell : 0≤ Shell) (hF : 0≤ F) (hA : 0≤ A)
    (hP : 0≤ Pz) (hl : 0≤ lower) (hL : 0≤ L) (hD : 0≤ D)
    (hc : 0≤ Control) (hb : 0≤ bro) (hq : 0≤ q) (hi : 0≤ volumeRoot)
    (hk : 0≤ kr) (hm : 0≤ mr) :
    E≤ Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*Control*bro*Rpow := by
  let rest := S*F*A*Pz*(lower/D)*Control*bro*(q*volumeRoot*kr*mr)
  have hrest : 0≤ rest := by dsimp only [rest]; positivity
  calc
    E≤(Ck*Cprof)*rest := by convert hpaid using 1; dsimp only [rest]; ring
    _≤ max 1 (Ck*Cprof)*rest := mul_le_mul_of_nonneg_right (le_max_right _ _) hrest
    _≤ max 1 (Ck*Cprof)*(Shell*F*A*Pz*(L/D)*Control*bro*Rpow) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (le_max_left _ _))
      dsimp only [rest]
      gcongr
    _=_ := by ring


private theorem error_norm_reference_orientation (reflected : Bool)
    (τ : Character) (l : FirstSourceLabel) (K X Z ξ sigma reserve r : ℝ) (p : O) (k : ℕ) :
    geometryExceptionalErrorReference τ
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex l.1.1 l.1.2=>q.val) l.2.val})
      K X Z sigma (frequencyLoss Z 32 ξ) reserve r p k=
    let I := if reflected then l.1.2 else l.1.1
    let H := if reflected then l.1.1 else l.1.2
    (X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
      Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (H.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6))*
      localErrorCost p (k-1)*(X/(I.absNorm:ℝ)/(normValue p)^k)^(1/3:ℝ)*
      (errorCommonRadius Z (Real.logb Z (H.absNorm:ℝ))
        (nominalLog l.1.1 l.1.2
          (Ideal.span {primeSubsetGenerator (fun q : CommonIndex l.1.1 l.1.2=>q.val) l.2.val}) K X Z)
        (Real.logb Z (I.absNorm:ℝ)) sigma (frequencyLoss Z 32 ξ) reserve p k)^(5/6:ℝ)*
      Z^(-2*max r 0/3) := by
  cases reflected
  · simp only [geometryExceptionalErrorReference,Bool.false_eq_true,↓reduceIte]
    ring
  · simp only [geometryExceptionalErrorReference,↓reduceIte]
    rw [nominalLog_swap l.1.1 l.1.2,active_span_swap l.1.1 l.1.2]
    ring



private theorem exceptional_error_mass_nonneg (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) :
    0≤ exceptionalPhysicalNormSum η χ Q m t S β W K Tsec Z ξ H := by
  unfold exceptionalPhysicalNormSum
  apply Finset.sum_nonneg; intro p _
  apply Finset.sum_nonneg; intro U _
  apply Finset.sum_nonneg; intro n _
  exact norm_nonneg _

attribute [local irreducible] exceptionalPhysicalNormSum

private theorem error_source_price_identity (P : Finset (Ideal O)) (w V A : ℝ)
    (p : O) (i : Fin 3) :
    errorNormalizedCoefficient P w V p i*A=
      (56/(P.card:ℝ))*(16*(errorIndex i+2:ℝ))*(w*localErrorCost p (errorIndex i)*(A/V)) := by
  unfold errorNormalizedCoefficient
  ring

private theorem error_norm_paid_replace
    (E side F qpre qfac A Ck Power Pz cap cost kr lower D Cprof pc hc mc bro root : ℝ)
    (hq : qpre=qfac) (hpower : Power=Pz*cap)
    (hpaid : E≤(side*F*qpre*A*(Ck*Power*kr*lower/D)*cost)*
      ((Cprof*pc*hc*mc)*(bro*root))) :
    E≤ side*F*qfac*A*(Ck*Pz*(cost*cap)*kr*lower/D)*
      (Cprof*(pc*hc*mc)*bro*root) := by
  rw [hq,hpower] at hpaid
  convert hpaid using 1
  ring

private theorem error_norm_zero_price_le (P : Finset (Ideal O))
    (w V A target : ℝ) (p : O) (i : Fin 3) (hw : w=0) (ht : 0≤ target) :
    errorNormalizedCoefficient P w V p i*A≤ target := by
  rw [hw]
  simpa only [errorNormalizedCoefficient,mul_zero,zero_mul,zero_div] using ht

private theorem error_norm_split_power (z a c : ℝ) (hz : 0< z) :
    z^(a-2*c/3)=z^a*z^(-2*c/3) := by
  calc
    _=z^(a+(-2*c/3)) := congrArg (fun e : ℝ=>z^e) (by ring)
    _=_ := Real.rpow_add hz a (-2*c/3)

private theorem error_lower_base_nonneg {α : Type*} [Fintype α]
    (u : Input α) (w : ℝ) : 0≤((∏a,u.lo a)*w*w) := by
  have hp : 0≤∏a,u.lo a := Finset.prod_nonneg (fun a _=>(u.lo_pos a).le)
  calc
    _=(∏a,u.lo a)*w^2 := by ring
    _≥0 := mul_nonneg hp (sq_nonneg w)

private theorem error_norm_allocation_sum {α : Type*} (A : Finset α)
    (fee G rad D : ℝ) :
    (∑_B : A,fee*(A.card:ℝ)*G/(rad*D))=fee*(A.card:ℝ)^2*G/(rad*D) := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  ring

set_option linter.unusedVariables false in
/-- Pure-data full extracted exceptional payment; its source gates are
arithmetic and profile receipts, and contain no exceptional energy premise. -/
def GeometryExceptionalErrorNormFullSpec
    (wlo whi : ℝ) (lo hi : ι→ℝ) (ε δ θ : ℝ) (η : Character)
    (b bs slotlo εalloc εcount ξ : ℝ) (J : ℕ) (Sp : Finset (ℕ×ℕ))
    (Ck : ℝ) (Qfix : Ideal O) (Kfix Cd Da Z : ℝ) : Prop :=
    ∀(hZ : 1< Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hend : Endpoints b bs bs s) (hlower : slotlo≤ s.lower) (hsP : ∀i,1≤ s.P i)
            (p0 : Profiles wlo whi) (hW₁ : s.W₁=p0.profile 0) (hW₂ : s.W₂=p0.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed) (hs0 : seed≠0)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤ Z^(2:ℝ)) (hsourcepos : 0< sourceRadius s)
            (hsource : sourceRadius s≤ Z^(3:ℝ)) (hlogV : |Real.logb Z (volume s)|≤3)
            (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤ Z) (amp reserve t v plainLoss : ℝ)
            (hamp : 0≤ amp) (hamp₁ : amp≤1) (hreserve : 0≤ reserve)
            (hω : frequencyLoss Z 32 ξ+reserve≤3)
            (hX₁ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
            (hX₂ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
            (hY₁ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
            (hY₂ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂)
            (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
            (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
            (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (key : ℤ×(Fin 5→ℤ))
            (Mprime : Ideal O) (hMprime : NeZero Mprime),
            letI : NeZero Mprime := hMprime
            ∀(Hprime : Subgroup (O⧸Mprime)ˣ) (Sbad : Finset (Ideal O))
              (hbad : fixedBadPrimes⊆Sbad),
            let P := CenteredMomentPrimePool.primePool Mprime Hprime Sbad (1/2) 1 (Z^amp)
            let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
            let rows := firstLiveColumns (geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key)
              (fun _=>logAnnulus)
            let firsts := GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ hK key
            ∀(υ : firsts→ elementPool P→ Fin 3→ RayCharacter→ Character)
              (hcop : ∀q : firsts,∀p∈elementPool P,∀j I,
                I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ hK key t q).slots j→
                  IsCoprime (Ideal.span {p}) I)
              (hυ : ∀q : firsts,∀p : elementPool P,∀i : Fin 3,∀ψ : RayCharacter,
                (υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
                  (geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hK key q.1.val) ψ)
                    fixedBadMask p.val (errorMovingExponent (errorIndex i)))
              (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m),
            let cost := fun j : rows=>∑B : actualAllocations s.pools
                (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hK key j.val),
              ∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
                ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
                  (Z^(1:ℝ)) Z ξ hK key t ⟨j,B⟩)).pools ((Ideal.span {p.val})^(errorIndex i+1)),
                  ∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
                    Z 1 amp ξ reserve b t hZ key ⟨j,B⟩ P p.val i Bp (υ ⟨j,B⟩ p i ψ) v Qfix m χ₀

            let Hshell := Z^((key.2 1:ℝ)*Real.logb Z 2)
            let Shell := if reflected then 1/Hshell
              else (4/((∏i,s.lo i)*a₁*a₂))^2*(2*Hshell)
            let Control := p0.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6
            let coef := max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
              (Fintype.card ι) b J Qfix Kfix)
            let factor := (56*128*3*8*(Fintype.card RayCharacter:ℝ)^2)*Shell*
              (fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^(Fintype.card ι)*
              coef*geometryExceptionalLowerConstant (Fintype.card ι) slotlo wlo*Control*
              (b^(Fintype.card ι))^(1/3:ℝ)*Da^2
            let exponent := 2*ε+2*δ+2*126*θ+Real.logb Z (geometryExceptionalVolume s)-
              (1+Real.logb Z (s.η.modulus.absNorm:ℝ))+
              3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3+3*εalloc
            (∑j : rows,cost j)≤ Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)

set_option maxHeartbeats 500000 in
set_option linter.defProp false in
/-- Saved actual exceptional kernels, reference contraction and the complete
extracted allocation/ray/prime menus. The original radical and projector are
summed jointly; the prime factor 56/P is paid once. -/
theorem actual_geometry_error_exceptional_norm_full
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (ε δ θ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0< slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1)  :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),
      ∀Qfix : Ideal O,Qfix≠0 → Qfix≠⊤ → Qfix≤ Ideal.span {(72:O)} →
      ∃Kfix Cd Da : ℝ,0< Kfix ∧ 0< Cd ∧ 0< Da ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧ GeometryExceptionalErrorNormFullSpec wlo whi lo hi ε δ θ η
          b bs slotlo εalloc εcount ξ J Sp Ck Qfix Kfix Cd Da Z := by
  let N := Fintype.card ι
  let closed := actual_geometry_error_exceptional_norm_closed wlo whi hwlo hwhi lo hi ballProfile
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
  refine ⟨J,Sp,Ck,?_⟩
  intro Qfix hQ hQt hQ72
  let saved := closed.2.2.2 Qfix hQ hQt hQ72
  let Kfix := saved.1
  let hevent := saved.2.1.down.2.and hCd.2
  refine ⟨Kfix,Cd,Da,saved.2.1.down.1,hCd.1,hDa.1,?_⟩
  filter_upwards [hevent] with Z hz
  let kernel := saved.2.2.down Z hz.1
  refine ⟨kernel.1,?_⟩
  unfold GeometryExceptionalErrorNormFullSpec
  intro hZ s hlo hhi hη hend hlower hsP p0 hW₁ hW₂ R seed hR hs hs0 hz₁ hz₂
    hV hsourcepos hsource hlogV hpool hRN amp reserve t v plainLoss hamp hamp₁ hreserve hω
    hX₁ hX₂ hY₁ hY₂ a₁ a₂ ha₁ ha₂ hs₁ hs₂ reflected Ψ key Mprime hMprime
  let : NeZero Mprime := hMprime
  intro Hprime Sbad hbad P hK rows firsts υ hcop hυ m hm hml hm2
  let cost := fun j : rows=>∑B : actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hK key j.val),
    ∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
      ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
        (Z^(1:ℝ)) Z ξ hK key t ⟨j,B⟩)).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        ∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
          Z 1 amp ξ reserve b t hZ key ⟨j,B⟩ P p.val i Bp (υ ⟨j,B⟩ p i ψ) v Qfix m χ₀
  have hZpos : 0< Z := zero_lt_one.trans hZ
  let Hshell := Z^((key.2 1:ℝ)*Real.logb Z 2)
  have hH : 0< Hshell := Real.rpow_pos_of_pos hZpos _
  have hphysical (j : rows) : Hshell≤
      ((geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key j.val.1).D.absNorm:ℝ) ∧
      ((geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key j.val.1).D.absNorm:ℝ)≤2*Hshell := by
    have hr := actual_geometry_fiber_range s R seed (Z^(1:ℝ)) Z ξ 3 hZ hs hz₁ hz₂
      hsource key j.val.1 1
    have hn := actual_geometry_norm_caps s R seed (Z^(1:ℝ)) Z ξ 3 hs hz₁ hz₂
      hsource j.val.1.val 1
    have hl := Real.rpow_le_rpow_of_exponent_le hZ.le hr.1
    have hu := Real.rpow_le_rpow_of_exponent_le hZ.le hr.2.le
    rw [geometryExponents,Real.rpow_logb hZpos hZ.ne' (zero_lt_one.trans_le hn.1)] at hl hu
    have he : Z^(((key.2 1:ℝ)+1)*Real.logb Z 2)=2*Hshell := by
      rw [add_mul,one_mul,Real.rpow_add hZpos,
        Real.rpow_logb hZpos hZ.ne' (by norm_num : (0:ℝ)<2)]
      exact mul_comm _ _
    exact ⟨hl,hu.trans_eq he⟩
  let Shell := if reflected then 1/Hshell
    else (4/((∏i,s.lo i)*a₁*a₂))^2*(2*Hshell)
  let Control := p0.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6
  let coef := max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
  let fee := 56*128*3*8*(Fintype.card RayCharacter:ℝ)^2
  let factor := fee*Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
    coef*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Da^2
  let exponent := 2*ε+2*δ+2*126*θ+Real.logb Z (geometryExceptionalVolume s)-
    (1+Real.logb Z (s.η.modulus.absNorm:ℝ))+
    3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3+3*εalloc
  have hShell : 0≤ Shell := by dsimp only [Shell]; split_ifs <;> positivity
  have hControl : 0≤ Control := by dsimp only [Control]; positivity
  have hfee : 0≤ fee := by dsimp only [fee]; positivity
  have hfixed : 0< fixedPresentationCost := fixedPresentationCost_pos
  have hLower : 0≤ geometryExceptionalLowerConstant N slotlo wlo :=
    Real.rpow_nonneg (by positivity) _
  have hfactor : 0≤ factor := by dsimp only [factor,coef]; positivity
  have hprimeP : ∀Q∈P,Prime Q := fun Q hQ=>
    (primePool_data Mprime Hprime Sbad hbad (1/2) 1 (Z^amp) Q hQ).1
  have hbadP : ∀Q∈P,Q∉fixedBadPrimes := fun Q hQ=>
    (primePool_data Mprime Hprime Sbad hbad (1/2) 1 (Z^amp) Q hQ).2
  have hc : ∀j : rows,0≤ cost j := by
    intro j
    apply Finset.sum_nonneg; intro B _
    apply Finset.sum_nonneg; intro p _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro ψ _
    apply Finset.sum_nonneg; intro Bp _
    apply Finset.sum_nonneg; intro χ₀ _
    unfold geometryExceptionalErrorNormSourceMass
    exact mul_nonneg (error_normalized_coefficient_nonneg _ _ _
      (geometryAllocationWeight_nonneg ..) (CenteredMomentAmplificationChildInput.volume_pos _) _ _)
      (exceptional_error_mass_nonneg ..)
  have hcost : ∀j : rows,cost j≤ factor*
      Z^(exponent-geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 2)/
        (j.val.2.1.val.absNorm:ℝ) := by
    intro j
    let I := geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hK key j.val
    let τ := geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hK key j.val
    let src := geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key j.val.1
    let l := geometryFirstLabel s R seed (Z^(1:ℝ)) Z ξ hK key j.val
    let rad := ((commonRadical src.C src.D).absNorm:ℝ)
    let Dproj := (j.val.2.1.val.absNorm:ℝ)
    let X := geometryExceptionalVolume s
    let Pz := Z^(2*ε+2*δ+2*126*θ)
    let Rpow := Z^(Real.logb Z X-(1+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3)
    let G := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
      coef*Pz*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Rpow
    have hG : 0≤ G := by dsimp only [G,coef,Pz,Rpow]; positivity
    have hrad : 0< rad := norm_pos _ (commonRadical_ne_zero _ _)
    have hDproj : 0< Dproj := norm_pos _
      (actual_first_live_squarefree (geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key)
        (fun _=>logAnnulus) j.val j.property).ne_zero
    have hrow : cost j≤ fee*((actualAllocations s.pools I).card:ℝ)^2*G/(rad*Dproj) := by
      have hmenu (B : actualAllocations s.pools I) :
          (∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
            ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
              (Z^(1:ℝ)) Z ξ hK key t ⟨j,B⟩)).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              ∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
                Z 1 amp ξ reserve b t hZ key ⟨j,B⟩ P p.val i Bp (υ ⟨j,B⟩ p i ψ) v Qfix m χ₀)≤
          fee*((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
        let q : firsts := ⟨j,B⟩
        let u1 := geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ hK key t q
        let f := fun (p : elementPool P) (i : Fin 3) (ψ : RayCharacter)
          (Bp : actualAllocations (activeInput u1).pools ((Ideal.span {p.val})^(errorIndex i+1)))
          (χ₀ : RayCharacter)=>geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
            Z 1 amp ξ reserve b t hZ key q P p.val i Bp (υ q p i ψ) v Qfix m χ₀
        have hE : 0≤((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) :=
          div_nonneg (mul_nonneg (Nat.cast_nonneg _) hG) (mul_pos hrad hDproj).le
        have hpoint : ∀p i ψ Bp χ₀,f p i ψ Bp χ₀≤
            (56/(P.card:ℝ))*128*(((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj)) := by
          intro p i ψ Bp χ₀
          dsimp only [f]
          by_cases hne : frozenCoefficient B.val I R s.ν s.W s.P≠0
          · let Bplift : actualAllocations (child s I R B τ t).pools
                ((Ideal.span {p.val})^(errorIndex i+1)) :=
              geometryExceptionalActiveLift reflected s R seed Z ξ t hZ key q p.val i Bp
            let u := geometryErrorChild reflected s R seed Z 1 ξ t hZ key q p.val i Bp (υ q p i ψ) v
            have hpdata := elementPool_data P hprimeP hbadP p.val p.property
            have hp : p.val≠0 := hpdata.1.ne_zero
            have hpN := (actual_geometry_exceptional_prime_cap Mprime Hprime Sbad hbad Z amp hZ
              (hamp₁.trans (by norm_num)) p.val p.property).2
            have hpayed := kernel.2 hZ s hlo hhi hη le_rfl hend hsP p0 hW₁ hW₂ R seed hR hs
              hz₁ hz₂ hV hsource hlogV hRN amp ξ reserve t hamp hamp₁ hξ hξ₁ hreserve hω
              a₁ a₂ ha₁ ha₂ hs₁ hs₂ reflected Ψ key q hne p.val hp hpN (hcop q p.val p.property)
              i Bp (υ q p i ψ) ψ v (hυ q p i ψ) χ₀ m hm hml hm2
            have href := actual_geometry_full_error_reference reflected s R seed 1 Z ξ amp reserve t
              hZ key j.val B Mprime Hprime Sbad hbad p.val p.property i Bplift (υ q p i ψ) v plainLoss
              hX₁ hX₂ hY₁ hY₂
            change geometryExceptionalErrorReference τ
              (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
              (Ideal.span {primeSubsetGenerator (fun q : CommonIndex l.1.1 l.1.2=>q.val) l.2.val})
              (Z^(1:ℝ)) X Z (3*amp) (frequencyLoss Z 32 ξ) reserve
              (inputCap Z (twiceChild s I R B τ t (Ideal.span {p.val})
                (errorIndex i+1) Bplift (υ q p i ψ) v)) p.val (errorIndex i+1)≤ Rpow at href
            rw [error_norm_reference_orientation reflected τ l (Z^(1:ℝ)) X Z ξ
              (3*amp) reserve _ p.val (errorIndex i+1)] at href
            let side := if reflected then 1/(src.D.absNorm:ℝ)
              else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ)
            let den := (τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
              Z^(max (3*Real.logb Z (I.absNorm:ℝ)-
                5*Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)-
                Real.logb Z ((Ideal.span {activeConductor src.C src.D}).absNorm:ℝ)) 0/6)
            let qfac := (X/(I.absNorm:ℝ))/den
            let root := (X/(I.absNorm:ℝ)/(normValue p.val)^(errorIndex i+1))^(1/3:ℝ)
            let kr := (geometryErrorSourceRadius reflected s R seed Z 1 amp ξ reserve hZ key q p.val i)^(5/6:ℝ)
            let cap := Z^(-2*max (inputCap Z u) 0/3)
            let lower := ((∏a,u.lo a)*wlo*wlo)^(-2/3:ℝ)
            let Epaid := geometryAllocationWeight reflected s R seed (Z^(1:ℝ)) Z ξ 1
              (Real.logb Z X) hK key (fun c=>normPhase (coordinateBlock s R seed Ψ
                (Z^(1:ℝ)) Z ξ c)) N b j.val B*localErrorCost p.val (errorIndex i)*
                (exceptionalPhysicalNormSum u.η χ₀ Qfix m u.t
                  (finiteColumns (Fintype.piFinset u.pools))
                  (coefficient u ((R*I)*(Ideal.span {p.val})^(errorIndex i+1)) j.val.2.1.val)
                  ballProfile (geometryErrorSourceRadius reflected s R seed Z 1 amp ξ reserve hZ key q p.val i)
                  (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ key q p.val i)
                  Z ξ (sourceRadius u)/geometryExceptionalVolume u)
            have hulower : u.lower=s.lower := by rfl
            have hlow := actual_geometry_exceptional_lower_factor u N slotlo wlo
              ((live_card_le Bplift.val).trans ((live_card_le B.val).trans le_rfl)) hslot
              (by rw [hulower]; exact hlower) hwlo
            have hside : side≤ Shell := by
              dsimp only [side,Shell]
              split_ifs
              · exact div_le_div_of_nonneg_left zero_le_one hH (hphysical j).1
              · exact mul_le_mul_of_nonneg_left (hphysical j).2 (sq_nonneg _)
            have hside0 : 0≤ side := by dsimp only [side]; split_ifs <;> positivity
            have hXpos : 0< X := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
            have hIpos : 0<(I.absNorm:ℝ) := norm_pos I (allocation_ne s I B)
            have hτpos : 0<(τ.modulus.absNorm:ℝ) := norm_pos τ.modulus τ.modulus_ne_bot
            have hq : 0≤ qfac := div_nonneg (div_nonneg hXpos.le hIpos.le)
              (mul_nonneg (mul_nonneg hτpos.le (sq_nonneg _)) (Real.rpow_nonneg hZpos.le _))
            have hbase := error_lower_base_nonneg u wlo
            have hlogs :
                (if reflected then max (3*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 1-
                  5*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 0-
                  geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 3) 0/6 else
                  max (3*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 0-
                    5*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 1-
                    geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 3) 0/6)=
                max (3*Real.logb Z (I.absNorm:ℝ)-
                  5*Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)-
                  Real.logb Z ((Ideal.span {activeConductor src.C src.D}).absNorm:ℝ)) 0/6 := by
              cases reflected <;> rfl
            let qpre := (X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
              Z^(if reflected then max (3*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 1-
                5*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 0-
                geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 3) 0/6 else
                max (3*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 0-
                  5*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 1-
                  geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 3) 0/6))
            have hqpre : qpre=qfac := by dsimp only [qpre,qfac,den]; rw [hlogs]
            have hsplit : Z^(2*ε+2*δ+2*126*θ-2*max (inputCap Z u) 0/3)=Pz*cap := by
              exact error_norm_split_power Z (2*ε+2*δ+2*126*θ)
                (max (inputCap Z u) 0) hZpos
            have hpaidRewrite := error_norm_paid_replace Epaid side
              (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/rad) qpre qfac
              ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)) Ck
              (Z^(2*ε+2*δ+2*126*θ-2*max (inputCap Z u) 0/3)) Pz cap
              (localErrorCost p.val (errorIndex i)) kr lower Dproj
              (CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
              (p0.control Sp^2) ((1+‖v‖)^(2*J)) ((∏a,s.M a)^6)
              ((b^N)^(1/3:ℝ)) root hqpre hsplit hpayed
            change qfac*localErrorCost p.val (errorIndex i)*root*kr*cap≤ Rpow at href
            have hfold := error_norm_fold_algebra Epaid side Shell
              (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/rad)
              ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)) Ck
              (CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
              Pz lower (geometryExceptionalLowerConstant N slotlo wlo) Dproj Control
              ((b^N)^(1/3:ℝ)) qfac root kr (localErrorCost p.val (errorIndex i)*cap) Rpow
              (by simpa only [Control] using hpaidRewrite)
              hside hlow
              (by convert href using 1; ring)
              hside0 hShell
              (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le)
              (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _) (Nat.cast_nonneg _))
              (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hbase _) hLower hDproj.le hControl
              (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hb) _) _) hq
              (Real.rpow_nonneg (div_nonneg (div_nonneg hXpos.le hIpos.le)
                (pow_nonneg (by unfold normValue; exact Nat.cast_nonneg _) _)) _)
              (Real.rpow_nonneg (actual_geometry_error_source_radius_pos reflected s R seed Z 1
                amp ξ reserve hZ key q p.val i).le _)
              (mul_nonneg (localErrorCost_nonneg _ _) (Real.rpow_nonneg hZpos.le _))
            have hpoint : Epaid≤((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
              convert hfold using 1; dsimp only [G,coef]; ring
            have hprice : geometryExceptionalErrorNormSourceMass reflected s R seed Ψ Z 1 amp ξ reserve b t
                hZ key q P p.val i Bp (υ q p i ψ) v Qfix m χ₀=
                (56/(P.card:ℝ))*(16*(errorIndex i+2:ℝ))*Epaid := by
              unfold geometryExceptionalErrorNormSourceMass
              rw [error_source_price_identity]
              rfl
            rw [hprice]
            have hprimecoef : 0≤56/(P.card:ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
            have hpricecoef : 0≤16*(errorIndex i+2:ℝ) :=
              mul_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le (errorIndex i+2)))
            exact (mul_le_mul_of_nonneg_left hpoint (mul_nonneg hprimecoef hpricecoef)).trans
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (error_index_price_cap i) hprimecoef) hE)
          · have hzweight : geometryAllocationWeight reflected s R seed (Z^(1:ℝ)) Z ξ 1
                (Real.logb Z (volume s)) hK key
                (fun c=>normPhase (coordinateBlock s R seed Ψ (Z^(1:ℝ)) Z ξ c)) N b j.val B=0 := by
              simp only [geometryAllocationWeight,I] at hne ⊢
              exact ite_eq_right hne
            exact error_norm_zero_price_le P _ _ _ _ p.val i hzweight
              (mul_nonneg (mul_nonneg
                (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num)) hE)
        have hh := error_menu_average_le u1 P hprimeP hbadP (hcop q)
          f (((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj)) hE hpoint
        calc
          _≤56*128*3*8*(Fintype.card RayCharacter:ℝ)^2*
              (((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj)) := hh
          _=_ := by dsimp only [fee]; ring
      calc
        _≤∑_B : actualAllocations s.pools I,fee*((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) :=
          Finset.sum_le_sum (fun B _=>hmenu B)
        _=_ := error_norm_allocation_sum (actualAllocations s.pools I) fee G rad Dproj
    have hI0 : I≠0 := by
      dsimp only [I,geometryColumnIdeal]
      split_ifs
      · exact src.hD.1
      · exact src.hC.1
    have hIcap : (I.absNorm:ℝ)≤ Z^(3:ℝ) := by
      dsimp only [I,geometryColumnIdeal]
      split_ifs
      · exact (actual_geometry_norm_caps s R seed (Z^(1:ℝ)) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 1).2
      · exact (actual_geometry_norm_caps s R seed (Z^(1:ℝ)) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 0).2
    have hcardalloc := hDa.2 (ι:=ι⊕Fin 2) (by simp only [N,Fintype.card_sum,Fintype.card_fin]; omega)
      s.pools I hI0
    have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardalloc 2
    rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),
      show εalloc/2*(2:ℕ)=εalloc by norm_num] at hcard2
    have hcardZ : ((actualAllocations s.pools I).card:ℝ)^2≤ Da^2*Z^(3*εalloc) := by
      apply hcard2.trans
      rw [Real.rpow_mul hZpos.le]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hIcap hea.le) (sq_nonneg _)
    apply hrow.trans
    have hrpow : Z^(geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 2)=rad :=
      Real.rpow_logb hZpos hZ.ne' hrad
    have hpow : Z^(3*εalloc)*Pz*Rpow=Z^exponent := by
      dsimp only [Pz,Rpow,exponent,X]
      rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos]
      congr 1; ring
    calc
      _≤ fee*(Da^2*Z^(3*εalloc))*G/(rad*Dproj) := by gcongr
      _=factor*Z^exponent/(rad*Dproj) := by
        dsimp only [factor,G]
        rw [←hpow]
        ring
      _=factor*Z^(exponent-geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 2)/Dproj := by
        rw [Real.rpow_sub hZpos,hrpow]; ring
  exact hz.2.2 s R seed (Z^(1:ℝ)) hK key hs hs0 hz₁ hz₂ hsourcepos hsource hV
    (by simpa only [Real.rpow_zero,Real.rpow_one] using (inv_le_one_of_one_le₀ hZ.le)) rows
    (fun j _=>actual_first_live_squarefree (geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key)
      (fun _=>logAnnulus) j (by assumption))
    (fun j _=>actual_geometry_projector_cap s N R seed (Z^(1:ℝ)) Z ξ 3 hK le_rfl hZ.le
      (by norm_num) hpool key j)
    factor exponent cost hfactor hc hcost

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_selected_norm_le

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_norm_full

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalErrorNormPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineExceptionalGates; sha256 b6daccf05ff82724ee5625695bef07e2eaa13c5368d6d37e150ba0b43b10fcde -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                       
                                                          
                                                            
                                                        
                                  
                                  

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CanonicalQuadraticSieve
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedRayDictionary CenteredMomentPrimeElements
open CenteredMomentCommonAllocationSum
open Cycle61InitialSource Cycle61Moment
local notation "O" => HeckeFamily.O

/-- Actual affine source receipts used by both exceptional payments. The
plain loss is the exact fixed-parent conductor logarithm divided by four. -/
structure GeometryAffineExceptionalSourceGates {ι : Type*} [Fintype ι]
    (s : Input ι) (p : Profiles (1/4) (9/4)) (N : ℕ) (Cs Z : ℝ) : Prop where
  card : Fintype.card ι≤ N
  controls : ∀i,s.M i≤ Cs
  lower : s.lower=1
  lo : s.lo=fun _=>1
  hi : s.hi=fun _=>2
  endpoints : Endpoints (9/4) (9/4) (9/4) s
  scales : ∀i,1≤ s.P i
  profile₁ : s.W₁=p.profile 0
  profile₂ : s.W₂=p.profile 1
  zero₁ : s.W₁ 0=0
  zero₂ : s.W₂ 0=0
  support₁ : ∀x,s.W₁ x≠0→(1/4:ℝ)≤ x
  support₂ : ∀x,s.W₂ x≠0→(1/4:ℝ)≤ x
  volume : CenteredMomentAmplificationChildInput.volume s≤ Z^(2:ℝ)
  volumeLog : |Real.logb Z (CenteredMomentAmplificationChildInput.volume s)|≤3
  sourcePositive : 0< sourceRadius s
  sourceCap : sourceRadius s≤ Z^(3:ℝ)
  poolCap : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^(3:ℝ)
  plain₁ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
    Real.logb Z (s.η.modulus.absNorm:ℝ)/4)≤ s.X₁
  plain₂ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
    Real.logb Z (s.η.modulus.absNorm:ℝ)/4)≤ s.X₂
  plain₃ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
    Real.logb Z (s.η.modulus.absNorm:ℝ)/4)≤ s.Y₁
  plain₄ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
    Real.logb Z (s.η.modulus.absNorm:ℝ)/4)≤ s.Y₂

private theorem affine_exceptional_quarter (Z X₁ X₂ ell : ℝ)
    (hZ : 1< Z) (hX₁ : 0< X₁) (_hX₂ : 0< X₂)
    (hlo₁ : (41/100:ℝ)≤ length Z X₁) (hlo₂ : (41/100:ℝ)≤ length Z X₂) :
    let r:=Z^((1+ell)/4-ell/4)
    r≤ X₁ ∧ r≤ X₂ ∧ r≤ comparisonFirst Z 1 ∧
      r≤ comparisonSecond Z 1 X₁ X₂ := by
  intro r
  have hr : r=Z^(1/4:ℝ) := congrArg (fun e : ℝ=>Z^e) (by ring)
  have hq : 0< Z^(1/4:ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hx (X : ℝ) (hlo : (41/100:ℝ)≤ length Z X) : Z^(1/4:ℝ)≤ X := by
    rw [initial_scale_exact Z X 1 hZ (by norm_num) (by simpa only [mul_one] using hlo)]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hx₁:=hx X₁ hlo₁
  have hx₂:=hx X₂ hlo₂
  rw [hr]
  refine ⟨hx₁,hx₂,le_rfl,?_⟩
  exact (le_div_iff₀ hq).mpr (mul_le_mul hx₁ hx₂ hq.le hX₁.le)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineExceptionalFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤ H)

/-- The threshold and profile cap precede every slot subset, smooth plain
profile, fixed-parent radial function, and both heights. No energy is assumed. -/
theorem eventual_actual_affine_exceptional_source_gates
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) :
    ∃Cs : ℝ,1≤ Cs ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(T : Finset α)(η₀ : Character)(θ : T→ RayQuotient.Characters rayM H)
        (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,0≤ w i) → (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) → (∑i,w i)≤(1/25:ℝ) →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      GeometryAffineExceptionalSourceGates inp p (Fintype.card α) Cs Z := by
  obtain ⟨Cs,bs,bp,hCs,hbs,hbp,hfixed⟩:=fixed_affine_source_caps (α:=α) rayM H hH W hW
    1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [eventual_affine_polynomial_caps (α:=α) rayM H hH W hW
      1 2 (33/50) (33/50) (1/4) (9/4) 1 (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (9/4:ℝ)] with Z hc hlarge
  refine ⟨hc.1,?_⟩
  intro T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi inp
  have hcaps:=hc.2 T η₀ θ w σ freq hσ bΦ state p 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) le_rfl hw (by simpa only [mul_one] using hlo₁)
    (by simpa only [mul_one] using hlo₂) (by simpa only [mul_one] using hhi₁)
    (by simpa only [mul_one] using hhi₂) (by simpa only [one_div] using hwhi)
  have hfixed':=hfixed T η₀ θ w σ freq hσ state p 1 t X₁ X₂ hX₁ hX₂
  have he:=affine_endpoints rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) (by norm_num)
  have hplain (j : Fin 2)(x : ℝ)(hne : p.profile j x≠0) : (1/4:ℝ)≤ x :=
    (p.support j hne).1
  have hzero (j : Fin 2) : p.profile j 0=0 := by
    by_contra hne
    have hh:=hplain j 0 hne
    norm_num at hh
  have hpool:=affine_individual_pool_cap rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    1 hc.1 (by norm_num) le_rfl (by norm_num)
    (by norm_num; linarith) hlarge hw (by simpa using hwhi) (by simpa using hhi₁) (by simpa using hhi₂)
  have hquarter:=affine_exceptional_quarter Z X₁ X₂
    (Real.logb Z (inp.η.modulus.absNorm:ℝ)) hc.1 hX₁ hX₂ hlo₁ hlo₂
  refine ⟨hfixed'.1,hfixed'.2.1,rfl,rfl,rfl,?_,?_,rfl,rfl,hzero 0,hzero 1,
    hplain 0,hplain 1,?_,?_,?_,?_,?_,hquarter.1,hquarter.2.1,hquarter.2.2.1,hquarter.2.2.2⟩
  · exact ⟨he.1.trans (by norm_num),he.2⟩
  · intro i
    exact Real.one_le_rpow hc.1.le (hw i)
  · simpa only [show (1:ℝ)+1=2 by norm_num] using hcaps.2.2.1
  · exact hcaps.2.1.trans (by norm_num)
  · change 0<(∏i : T,(2:ℝ))*(9/4)*(9/4)*(X₁*X₂)*(∏i : T,Z^(w i))
    exact mul_pos (mul_pos (mul_pos (mul_pos (Finset.prod_pos (fun _ _=>by norm_num))
      (by norm_num)) (by norm_num)) (mul_pos hX₁ hX₂))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (zero_lt_one.trans hc.1) _))
  · simpa only [show (1:ℝ)+2=3 by norm_num] using hcaps.2.2.2.1
  · intro i I hI
    exact (hpool i I hI).trans (Real.rpow_le_rpow_of_exponent_le hc.1.le (by norm_num))

/-- Actual amplifier primes are coprime to every stored first-child slot,
including slots whose smooth coefficient vanishes. The first allocation
and both heights are chosen after the common scale threshold. -/
theorem eventual_actual_affine_exceptional_child_coprime
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (mesh : ℝ) (hmesh : mesh<(62485051/9854400000:ℝ)/2) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{ι : Type*}[Fintype ι][DecidableEq ι]
        (η₀ : Character)(θ : ι→ RayQuotient.Characters rayM H)
        (w σ freq : ι→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
      (∀i,w i≤ mesh) → ∀beta : ℝ,3401/100000≤ beta → beta≤1/25 →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(Cycle61.Arithmetic.amp beta))
      ∀(q : elementPool P)(C R : Ideal O)(B : actualAllocations inp.pools C)
        (τ : Character)(height : ℝ),
      ∀i I,I∈(child inp C R B τ height).slots i→ IsCoprime (Ideal.span {q.val}) I := by
  filter_upwards [eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh]
    with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hwm beta hb₁ hb₂ inp P q C R B τ height
  have hm : Matches rayM H hH inp η₀ θ w σ freq W 2 Z := by
    constructor <;> intros <;> rfl
  exact actual_child_full_slot_coprime inp (Ideal.span {q.val})
    (hz.2 beta hb₁ hb₂ inp η₀ θ w σ freq W hm hwm q) C R B τ height

/-- Fixed-parent specialization retains the exact conductor; it does not
require a threshold uniform over arbitrary moving NaturalState characters. -/
theorem affine_exceptional_fixed_parent_character (η : Character) (Q : Ideal O)
    (Φ : 𝓢(ℝ,ℂ)) (bΦ Z : ℝ) (hZ : 1< Z)
    (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ) (hp : ∀x,0≤(Φ x).re) :
    (fixedParentState η Q Φ bΦ Z 1 hZ (by norm_num) hs hp).character=η ∧
      (fixedParentState η Q Φ bΦ Z 1 hZ (by norm_num) hs hp).characterWidth=
        Real.logb Z (η.modulus.absNorm:ℝ) := ⟨rfl,rfl⟩

/-- The literal logarithmic volume is paid by the original canonical cell,
before extraction changes any child scale or allocation. -/
theorem affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (Z n₁ n₂ slots : ℝ)
    (hvolume : Real.logb Z (volume s)=n₁+n₂+slots)
    (hslots : (17/500:ℝ)≤ slots ∧ slots≤1/25)
    (hcone : n₁+n₂+Cycle61.Arithmetic.lambda*slots≤ Cycle61.Arithmetic.B) :
    Real.logb Z (volume s)≤ Cycle61.Arithmetic.totalA
      (Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell slots)) := by
  have hh:=Cycle61.Moment.normalized_cell_bounds (M:=1) (n₁:=n₁) (n₂:=n₂)
    (z:=slots) (by norm_num) (by simpa only [mul_one] using hslots)
    (by simpa only [mul_one] using hcone)
  simpa only [div_one,one_mul,hvolume] using hh.2.2.2.1

/-- The canonical-cell ledger applied to the literal affine input; the
volume identity is proved here, rather than supplied as a source premise. -/
theorem actual_affine_exceptional_volume_cell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η₀ : Character) (θ : ι→ RayQuotient.Characters rayM H)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : ι→ℝ) (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hZ : 1< Z)
    (hlo₁ : (41/100:ℝ)≤ length Z X₁) (hlo₂ : (41/100:ℝ)≤ length Z X₂)
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    Real.logb Z (volume inp)≤ Cycle61.Arithmetic.totalA
      (Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑i,w i))) := by
  intro inp
  apply affine_exceptional_volume_cell inp Z (length Z X₁) (length Z X₂) (∑i,w i) _ hslots hcone
  exact affine_volume_log_exact rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂ hZ
    (by norm_num) (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hlo₂)

/-- These are the main exponent after its one prime cancellation and the
extracted-error exponent after its already included 56/P payment. All
density, shell, frequency and height fees are charged to loss. -/
theorem affine_exceptional_exponent_saving (beta logV ell loss : ℝ)
    (hbeta : 3401/100000≤ beta ∧ beta≤1/25)
    (hV : logV≤ Cycle61.Arithmetic.totalA beta) (hell : 0≤ ell) (hloss : loss≤1/100) :
    loss+logV-(1+ell)+4*Cycle61.Arithmetic.amp beta+2*(ell/4)/3≤-(1/100:ℝ) ∧
      loss+logV-(1+ell)+3*(3*Cycle61.Arithmetic.amp beta)/2+2*(ell/4)/3≤-(1/100:ℝ) := by
  have hm:=Cycle61.Arithmetic.main_fixed_reserve hbeta
  have he:=Cycle61.Arithmetic.error_fixed_reserve hbeta
  have ha:=(Cycle61.Arithmetic.amp_pos hbeta).le
  constructor <;> linarith

/-- One concrete choice pays the larger error density exponent 252, the
original label/projector shell, and both independent height windows. -/
theorem affine_exceptional_small_loss (εaffine omega heightLoss primeLoss : ℝ)
    (hε : 0<εaffine)
    (hω : omega≤33*geometryLossUnit 1 εaffine/128)
    (hh : heightLoss≤ geometryLossUnit 1 εaffine/8)
    (hp : primeLoss≤ geometryLossUnit 1 εaffine/8) :
    let μ:=geometryLossUnit 1 εaffine
    0<μ/128 ∧ 0<μ/2048 ∧
      2*(μ/128)+2*(μ/128)+252*(μ/2048)+5*omega/6+
        3*(μ/128)+3*(μ/128)+heightLoss+primeLoss≤1/100 := by
  intro μ
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hcap : μ≤1/128 := by
    exact (min_le_right (εaffine/128) _).trans
      ((min_le_right ((7/30000000)*1/128) _).trans (min_le_right (1/128) (1/128)))
  refine ⟨by positivity,by positivity,?_⟩
  change omega≤33*μ/128 at hω
  change heightLoss≤μ/8 at hh
  change primeLoss≤μ/8 at hp
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_exceptional_source_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_exceptional_child_coprime
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_exceptional_fixed_parent_character
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_exceptional_volume_cell
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_exceptional_volume_cell
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_exceptional_exponent_saving
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_exceptional_small_loss

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineExceptionalGates -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalPhaseNormPayment; sha256 726ab7daaa4e142de1a15f9f98c3dc3573d8e5e8050bf411821bd568e9b1c698 -/
section
                                                                  

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical SchwartzMap
open CenteredMomentFirstAnnularInput
open HeckeFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The main exceptional consumer keeps the arbitrary first detector independent
of the second ball-profile norm. Saved constants precede the detector and all
moving source, allocation, ray and height data. -/
def actual_geometry_main_exceptional_phase_norm_payment
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (ε δ θ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0< slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1) :=
  actual_geometry_main_exceptional_norm_payment wlo whi hwlo hwhi lo hi
    ε δ θ hε hδ hθ η b bs hb hbs slotlo εalloc εcount ξ hslot hea hec hξ hξ₁

/-- The extracted exceptional consumer has independent first detector and
second ball-profile norm, independent first/second heights, and the literal
factor 56/P exactly once. Its saved constants precede these moving data. -/
theorem actual_geometry_error_exceptional_phase_norm_payment
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (ε δ θ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0< slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),
      ∀Qfix : Ideal O,Qfix≠0 → Qfix≠⊤ → Qfix≤ Ideal.span {(72:O)} →
      ∃Kfix Cd Da : ℝ,0< Kfix ∧ 0< Cd ∧ 0< Da ∧
        ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧ GeometryExceptionalErrorNormFullSpec wlo whi lo hi ε δ θ η
          b bs slotlo εalloc εcount ξ J Sp Ck Qfix Kfix Cd Da Z :=
  actual_geometry_error_exceptional_norm_full wlo whi hwlo hwhi lo hi
    ε δ θ hε hδ hθ η b bs hb hbs slotlo εalloc εcount ξ hslot hea hec hξ hξ₁

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_phase_norm_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_phase_norm_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalPhaseNormPayment -/
