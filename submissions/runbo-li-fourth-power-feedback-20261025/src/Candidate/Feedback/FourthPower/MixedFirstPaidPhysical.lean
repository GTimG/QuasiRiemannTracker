/- Copyright (c) 2026 Sil. Apache-2.0.
The actual first physical block paid by the mixed numerical gates.
Only unit-prefix sources are asserted here; exact rebase is separate.
No moment, energy, or window estimate is a hypothesis.
-/
import Candidate.Feedback.FourthPower.MixedFirstPhysicalBudget
import Candidate.Feedback.FourthPower.MixedFirstPaidCosts
import Candidate.Feedback.FourthPower.MixedFirstCommonSum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedFirstPaidPhysical
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ConcreteTraceCRT RayFourExpansion ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource MixedFirstActualNonexceptional
open CenteredMomentFirstColumns CenteredMomentRankinRadical
open CenteredMomentCanonicalFirst CenteredMomentFirstMixedAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstWindowBudgets
open CenteredMomentFirstDiscardedEnergy CenteredMomentSourceRow CenteredMomentWholeDivisorShell
open CenteredMomentHeckeColumnWindow CenteredMomentSmoothedWindowEnergy
open CenteredMomentHeckeWindowEnergy CenteredMomentSecondWindowBudget CenteredMomentSecondWindowSource
open CenteredMomentGaussEnergy CenteredMomentNaturalFixedRaySource CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open CenteredMomentCauchy CenteredMomentSmooth FourierBridge
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget MixedPrincipalCentered
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalNormCap MixedOriginalTail
open MixedOriginalSecondZero MixedFirstLiveSource MixedFirstFourParts
open MixedFirstNonexceptionalAllocation MixedFirstNonexceptionalNormalization
open MixedFirstReferencePair MixedFirstInactiveConductor
open MixedFirstExceptionalNormalization MixedFirstExceptionalWindow MixedFirstExceptionalApplication
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstFullBudget MixedFirstAveragedWindow MixedHeightEnvelope MixedFirstAvoidance
open MixedFirstIntegratedWindows MixedFirstPhysicalApplication MixedFirstPhysicalBudget
open MixedFirstPaidCosts MixedFirstGeometricCaps
open ReferencePrimeEnclosure MixedCompletedRows QuadraticInitialBound EisensteinSchwartzPoisson
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The four actual fixed/profile coefficients after an exact unit-prefix
rebase. No source length, Z, common label, frequency index, ray, or
artificial divisor is present. Heights and ordinary-profile seminorms
remain explicit and the degrees are the previously selected controls. -/
def unitOriginalFactor (U : Controls) (s : Source ι a b) (Q : Id) : ℝ :=
  fixedQCost Q*(sourceProfile s U.exceptionalDegree U.exceptionalControl 1 0)^2*
    (16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ)*
    ((∏i,s.M i)^2*((2:ℝ)^Fintype.card ι)^(4/3:ℝ))

def unitCoefficients (U : Controls) (c : Constants) (s : Source ι a b)
    (Q : Id) (c0 t V : ℝ) : Fin 4→ℝ :=
  ![16*‖paperRadialFourier ballProfile 0‖*c.zero*(∏i,s.M i)^2*(profileCap s)^2*
      supportConstant b (Fintype.card ι),
    c.nonexceptionalCount*profileFactor s U.nonexceptionalDegree c.physical c.geometry
      (canonicalProfile U c s t V) 0,
    (c.kernel*c.exceptional*heightBase 0^(2*U.exceptionalDegree)*(windowMoment U.exceptionalDegree)^2)*
      c.exceptionalSum*c.exceptionalCount*unitOriginalFactor U s Q*c0^(-2/3:ℝ),
    c.tail*(∏i,s.M i)^2*(profileCap s)^2*
      U.tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile/c0^4]

theorem unit_coefficients_eq (U : Controls) (c : Constants) (s : Source ι a b)
    (hunit : s.d=(1,1)) (Q : Id) (c0 t V : ℝ) :
    coefficients U c s Q c0 t V 0=unitCoefficients U c s Q c0 t V := by
  funext i
  fin_cases i <;>
    simp [MixedFirstPaidCosts.coefficients,unitCoefficients,unitOriginalFactor,originalFactor,slotCost,
      hunit,pairNorm,prefixNormMax]

theorem unit_coefficients_nonneg (U : Controls) (c : Constants) (s : Source ι a b)
    (ha : 0<a) (hunit : s.d=(1,1)) (Q : Id) (c0 t V : ℝ)
    (hc0 : 0<c0) (hV : 0≤V) : ∀i,0≤unitCoefficients U c s Q c0 t V i := by
  rw [←unit_coefficients_eq U c s hunit Q c0 t V]
  exact coefficients_nonneg U c s ha Q c0 t V 0 hc0 hV

/-- This envelope is derived from the literal four coefficients. In
particular it is not a hypothesis on the energy or the profiles. -/
def profileEnvelope (U : Controls) (c : Constants) (s : Source ι a b)
    (Q : Id) (c0 t V : ℝ) : ℝ :=
  windowMass (degree U) t^2*(4*∑i : Fin 4,unitCoefficients U c s Q c0 t V i)

theorem profileEnvelope_nonneg (U : Controls) (c : Constants) (s : Source ι a b)
    (ha : 0<a) (hunit : s.d=(1,1)) (Q : Id) (c0 t V : ℝ)
    (hc0 : 0<c0) (hV : 0≤V) : 0≤profileEnvelope U c s Q c0 t V :=
  mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun i _=>unit_coefficients_nonneg U c s ha hunit Q c0 t V hc0 hV i)))

private theorem sixteen_le_four_sum (c : Fin 4→ℝ) (hc : ∀i,0≤c i) :
    (∑i : Fin 4,∑j : Fin 4,Real.sqrt (c i*c j))≤4*∑i : Fin 4,c i := by
  have hpair (i j : Fin 4) : Real.sqrt (c i*c j)≤(c i+c j)/2 := by
    rw [Real.sqrt_mul (hc i)]
    nlinarith [Real.sq_sqrt (hc i),Real.sq_sqrt (hc j),
      sq_nonneg (Real.sqrt (c i)-Real.sqrt (c j))]
  calc
    _≤∑i : Fin 4,∑j : Fin 4,(c i+c j)/2 :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hpair i j))
    _=_ := by
      simp only [add_div,Finset.sum_add_distrib,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,←Finset.sum_div]
      ring

def rayMass : ℝ := ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖

theorem rayMass_nonneg : 0≤rayMass :=
  Finset.sum_nonneg (fun χ _=>Finset.sum_nonneg (fun ξ _=>norm_nonneg _))

def artificialMass (s : Source ι a b) (C D : Id) (hD : D≠0) : ℝ :=
  ∑Dart∈artificialDivisors s C D hD,
    ‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖/(Dart.absNorm:ℝ)

theorem artificialMass_nonneg (s : Source ι a b) (C D : Id) (hD : D≠0) :
    0≤artificialMass s C D hD :=
  Finset.sum_nonneg (fun Dart _=>div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

/-- Both fixed-pair sides are the actual sides, with their own swapped
common data and their own nominal child scale. No equality KL=KR is used. -/
private theorem fixed_pair_paid (U : Controls) (c : Constants) (s : Source ι a b)
    (ha : 0<a) (hb : 0<b) (hunit : s.d=(1,1)) (η : Character) (Q : Id)
    (w : ι→ℝ) (t V : ℝ) (hV : 0≤V) (p : Parameters) (hp : Gates p)
    (g : SourceGeometry p s η w) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D))
    (hCcap : (C.absNorm:ℝ)≤p.Z^p.BG) (hDcap : (D.absNorm:ℝ)≤p.Z^p.BG)
    (hfirst : p.Tfirst≤p.Cfirst*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E})
      p.Kfirst (sourceVolume s))
    (n : ℤ) (hret : Retained (frequencyRadius p.Tfirst p.Z p.ξfirst) n)
    (Dart : Id) (hDart : Dart≠0) (χ ξ : RayCharacter) :
    (∑i : Fin 4,∑j : Fin 4,
      Real.sqrt (
        normalizedCosts U c s η (fixedPair η C D hC E χ (ξ⁻¹)).left C D Dart Q w p.Bnorm
          p.Z p.ε p.δ (3/4) t V 0 (sharpSupport s) p.Kfirst
          (nominalChildScale C D E p.Kfirst (sourceVolume s) p.Z p.κpad n)
          p.Cfirst p.ξfirst p.κpad p.W p.saving i *
        normalizedCosts U c s η (fixedPair η C D hC E χ (ξ⁻¹)).right D C Dart Q w p.Bnorm
          p.Z p.ε p.δ (3/4) t V 0 (sharpSupport s) p.Kfirst
          (nominalChildScale D C (swapSubset C D E) p.Kfirst (sourceVolume s) p.Z p.κpad n)
          p.Cfirst p.ξfirst p.κpad p.W p.saving j))≤
      (p.Z^p.loss*(4*∑i : Fin 4,unitCoefficients U c s Q p.c0 t V i))/(Dart.absNorm:ℝ) := by
  let F:=fixedPair η C D hC E χ (ξ⁻¹)
  let left : Side p s η :=
    { G:=C,Gopp:=D,τ:=F.left,height:=0,E:=E,n:=n,hG:=hC,hGopp:=hD,
      common:=hCD,cap:=hCcap,modulus:=F.left_modulus,frequency:=hfirst,retained:=hret }
  let right : Side p s η :=
    { G:=D,Gopp:=C,τ:=F.right,height:=0,E:=swapSubset C D E,n:=n,hG:=hD,hGopp:=hC,
      common:=hCD.symm,cap:=hDcap,modulus:=right_modulus η C D hC E χ (ξ⁻¹) F,
      frequency:=by simpa only [swapSubset_generator,nominal_swap] using hfirst,retained:=hret }
  have hpaid := actual_sixteen_pairs_paid U c s ha hb η Dart Q hDart w t V hV p hp g left right
  have hsum := sixteen_le_four_sum (unitCoefficients U c s Q p.c0 t V)
    (unit_coefficients_nonneg U c s ha hunit Q p.c0 t V hp.hc0 hV)
  change _≤p.Z^p.loss/(Dart.absNorm:ℝ)*
    ∑i : Fin 4,∑j : Fin 4,Real.sqrt (coefficients U c s Q p.c0 t V 0 i*
      coefficients U c s Q p.c0 t V 0 j) at hpaid
  rw [unit_coefficients_eq U c s hunit Q p.c0 t V] at hpaid
  have hh := hpaid.trans (mul_le_mul_of_nonneg_left hsum
    (div_nonneg (Real.rpow_nonneg (zero_lt_one.trans hp.hZ).le _) (Nat.cast_nonneg _)))
  convert hh using 1 <;> (try rfl) <;> ring

private theorem projector_majorant (Ls : Finset Id) (H : ℝ) (B : Id→RayCharacter→RayCharacter→ℝ)
    (hb : ∀Dart∈Ls,(UniqueFactorizationMonoid.moebius Dart:ℂ)≠0→∀χ ξ,
      B Dart χ ξ≤H/(Dart.absNorm:ℝ)) :
    (∑Dart∈Ls,‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖*
      ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*B Dart χ ξ)≤
      H*rayMass*∑Dart∈Ls,‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖/(Dart.absNorm:ℝ) := by
  calc
    _≤∑Dart∈Ls,‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖*
      ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*(H/(Dart.absNorm:ℝ)) := by
      apply Finset.sum_le_sum
      intro Dart hDart
      by_cases hμ : (UniqueFactorizationMonoid.moebius Dart:ℂ)=0
      · simp only [hμ,norm_zero,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=>
          Finset.sum_le_sum (fun ξ _=>mul_le_mul_of_nonneg_left
            (hb Dart hDart hμ χ ξ) (norm_nonneg _)))) (norm_nonneg _)
    _=_ := by
      simp only [←Finset.sum_mul]
      unfold rayMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Dart hDart
      ring

/-- The fourth-power push costs an explicit 5*Btail*epsilon. The factor
16^epsilon and selected weight mass are kept as fixed multipliers. -/
theorem pushCost_upper (Z B ε Cpush mass KL KR W : ℝ)
    (hZ : 0<Z) (hε : 0≤ε) (hC : 0≤Cpush) (hmass : 0≤mass)
    (hKL : 0≤KL) (hKR : 0≤KR) (hW : 0≤W)
    (hcL : KL≤Z^B) (hcR : KR≤Z^B) (hcW : W≤Z^B) :
    pushCost Cpush mass KL KR W ε≤mass*Cpush*(16:ℝ)^ε*Z^(5*B*ε) := by
  have hbound (K : ℝ) (hK : 0≤K) (hcK : K≤Z^B) :
      mass*Cpush*(16*K*W^4)^ε≤mass*Cpush*(16:ℝ)^ε*Z^(5*B*ε) := by
    have hbase : 16*K*W^4≤16*Z^(5*B) := by
      calc
        _≤16*(Z^B)*(Z^B)^4 := mul_le_mul
          (mul_le_mul_of_nonneg_left hcK (by norm_num))
          (pow_le_pow_left₀ hW hcW 4) (pow_nonneg hW _) (by positivity)
        _=_ := by
          rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
          rw [mul_assoc,←Real.rpow_add hZ]
          congr 2
          ring
    have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase hε)
      (mul_nonneg hmass hC)
    convert hh using 1 <;>
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤16) (Real.rpow_nonneg hZ.le _),
        ←Real.rpow_mul hZ.le] <;> ring
  let B0:=mass*Cpush*(16:ℝ)^ε*Z^(5*B*ε)
  have hB0 : 0≤B0 := by dsimp only [B0];positivity
  have hl := Real.sqrt_le_sqrt (hbound KL hKL hcL)
  have hr := Real.sqrt_le_sqrt (hbound KR hKR hcR)
  calc
    _≤Real.sqrt B0*Real.sqrt B0 :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _=B0 := by rw [←pow_two,Real.sq_sqrt hB0]

theorem unit_reference_prefactor (s : Source ι a b) (hunit : s.d=(1,1))
    (η : Character) (C D : Id) (E : Finset (CommonIndex C D)) (K : ℝ) :
    referencePrefactor s η C D E K (Real.log 4)=
      (4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*
        MixedFirstCommonSum.commonWeight C D E := by
  rw [MixedFirstCommonSum.common_weight_physical]
  simp only [referencePrefactor,hunit,pairNorm,mul_one,map_one,Nat.cast_one,div_one,
    Real.exp_log (by norm_num : (0:ℝ)<4)]
  ring

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- A quantitative bound for the original selected physical average.
The constants and threshold are selected before all source/profile data.
The remaining hypotheses are canonical data identities, literal scale
caps, and the already proved numerical Gates/SourceGeometry. All actual
energy estimates are supplied by uniform_physical_budget itself.

The loss is displayed as loss+5*Btail*epsilon. The common/artifical weight
is exactly the one summed by uniform_common_artificial_band_mass. -/
theorem uniform_paid_physical
    (Φ : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BG BH Bsource Bη Pexp Mgeom Btail
      ε δ lo hi ξsecond saving : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hMcap0 : 0<Mcap)
    (hL : 0≤L) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBG : 0≤BG) (hBH : 0≤BH) (hBsource : 0≤Bsource)
    (hPexp : 0≤Pexp) (hMgeom : 0≤Mgeom) (hBtail : 0≤Btail) (hBGtail : BG≤Btail)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hgap : (7/10:ℝ)+2*δ<1) (hξsecond : 0<ξsecond)
    (hMcap : Mgeom+(Bη+BG+ε)+Bsource+ε≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃U : Controls,∃Cpush Ckernel : ℝ,0<Cpush ∧ 0≤Ckernel ∧
    ∀η₀ : Character,Q≤η₀.modulus→∃c : Constants,
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t R₀ s→
      s.d=(1,1)→
      (s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      sourceNormCap s.P b s.T s.d≤Z^Bsource→poolCap s≤Z^Btail→
      (∏i,s.P i)≤Z^Pexp→(s.Fhole.absNorm:ℝ)≤Z^BH→
    ∀cover : OriginalEnclosure s,∀(η : Character)(C D : Id)(hC : Supported C)(hD : Supported D),
      primeSupport C=primeSupport D→
      (η.modulus.absNorm:ℝ)≤Z^Bη→(C.absNorm:ℝ)≤Z^BG→(D.absNorm:ℝ)≤Z^BG→
    ∀E : Finset (CommonIndex C D),E∈inactiveSubsets C D→
    ∀(Kfirst Tfirst Cfirst ξfirst κpad W : ℝ),0<Kfirst→0<W→1≤Cfirst→0≤ξfirst→
      Tfirst≤Cfirst*firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) Kfirst (sourceVolume s)→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀Tsecond : ℝ,0≤Tsecond→Tsecond≤Z^(Mgeom-ξsecond)→
      1≤sharpSupport s→(2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d≤sharpSupport s→
      sharpSupport s≤Z^Btail→W≤Z^Btail→W⁻¹≤Z^Btail→Tsecond≤Z^Btail→
    ∀n : ℤ,Retained (frequencyRadius Tfirst Z ξfirst) n→
    let KL:=nominalChildScale C D E Kfirst (sourceVolume s) Z κpad n
    let KR:=nominalChildScale D C (swapSubset C D E) Kfirst (sourceVolume s) Z κpad n
    KL≤Z^Btail→KR≤Z^Btail→sharpSupport s^2/(16*KL*W^4)≤Tsecond→
      sharpSupport s^2/(16*KR*W^4)≤Tsecond→
    ∀seed : Id,seed∣C→seed∣D→∀u : Id,u∣s.R*C→u∣s.R*D→
    let sActual:=avoidSource s u
    ∀(Ds : Finset Id)(rows : Finset O),
      (∀F∈Ds,Supported F)→(∀z∈rows,z≠0)→
    ∀(weight : Id→ℝ)(mass : ℝ),0≤mass→
      (∀F∈Ds,0≤weight F∧weight F≤mass)→(∀F∈Ds,(F.absNorm:ℝ)≤2*W)→
      (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤KL)→
      (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤KR)→
      (∀Dart∈artificialDivisors sActual C D hD.1,
        (UniqueFactorizationMonoid.moebius Dart:ℂ)≠0→(Dart.absNorm:ℝ)≤Z^Btail)→
    ∀K₀ H₀ A₀ B₀ : ℝ,0<K₀→0<H₀→0<A₀→0<B₀→
    ∀Rexp Praw Sraw dsel lref c0 omega sigma loss BX : ℝ,
    let p : Parameters :=
      { Z:=Z,Kfirst:=Kfirst,Tfirst:=Tfirst,Cfirst:=Cfirst,ξfirst:=ξfirst,κpad:=κpad,W:=W,
        ε:=ε,δ:=δ,Bnorm:=normExponent L Pexp ε,BG:=BG,BX:=BX,R:=Rexp,P:=Praw,S:=Sraw,
        d:=dsel,l:=lref,c0:=c0,omega:=omega,sigma:=sigma,loss:=loss,saving:=saving }
    Gates p→SourceGeometry p s η w→
    (1+K₀*H₀/(A₀*B₀))^decay*
      ‖physicalAverage sActual ha seed η t C D hC hD E rows Ds weight W Φ Kfirst K₀ H₀ A₀ B₀‖/
        sourceVolume s≤
      ‖commonHeight sActual η t C D‖*(4/a^2)*fixedPresentationCost*
        ((η.modulus.absNorm:ℝ)*Kfirst)*Ckernel*(mass*Cpush*(16:ℝ)^ε)*
        Z^(loss+5*Btail*ε)*profileEnvelope U c s Q c0 t V*rayMass*
        MixedFirstCommonSum.commonWeight C D E*artificialMass sActual C D hD.1 := by
  obtain ⟨U,Cpush,Ckernel,hCpush,hCkernel,hbound⟩ := uniform_physical_budget
    (ι:=ι) M Hray hHray Φ decay N Holes hcard Wslot a b Mcap L Lslot Lcap Cap
    BR BG BH Bsource Bη Pexp Mgeom Btail ε δ lo hi ξsecond saving
    hWs hW ha haUpper hb hMcap0 hL hLslot hLcap hCap hBR hBG hBH hBsource hPexp
    hMgeom hBtail hBGtail hCapb hLordinary hε hδ hgap hξsecond hMcap hβ Q hQt hQ72 hQM
  refine ⟨U,Cpush,Ckernel,hCpush,hCkernel,?_⟩
  intro η₀ hη₀
  obtain ⟨c,hbound⟩ := hbound η₀ hη₀
  refine ⟨c,?_⟩
  filter_upwards [hbound] with Z hz
  obtain ⟨hZ,hbound⟩ := hz
  refine ⟨hZ,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit hR hH hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η C D hC hD hCD hη hCcap hDcap
    E hE Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst hξfirst hfirst
    χ₀ msecond hm hml hm2 Tsecond hT hTcap hX hXcap hXupper hWupper hWinv hTupper
    n hret KL KR hKLcap hKRcap hTL hTR seed hseedC hseedD u huC huD sActual
    Ds rows hDs hrows weight mass hmass hweight hDN hKLrows hKRrows hDartCap
    K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀ Rexp Praw Sraw dsel lref c0 omega sigma loss BX p hp g
  let left:=fun (Dart : Id) (χ ξ : RayCharacter)=>normalizedCosts U c s η
    (fixedPair η C D hC E χ (ξ⁻¹)).left C D Dart Q w (normExponent L Pexp ε)
    Z ε δ (3/4) t V 0 (sharpSupport s) Kfirst KL Cfirst ξfirst κpad W saving
  let right:=fun (Dart : Id) (χ ξ : RayCharacter)=>normalizedCosts U c s η
    (fixedPair η C D hC E χ (ξ⁻¹)).right D C Dart Q w (normExponent L Pexp ε)
    Z ε δ (3/4) t V 0 (sharpSupport s) Kfirst KR Cfirst ξfirst κpad W saving
  let budget:=fun (Dart : Id) (χ ξ : RayCharacter)=>
    ∑i : Fin 4,∑j : Fin 4,Real.sqrt (left Dart χ ξ i*right Dart χ ξ j)
  let coeff:=4*∑i : Fin 4,unitCoefficients U c s Q c0 t V i
  have hcoeff : 0≤coeff := mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun i _=>unit_coefficients_nonneg U c s ha hunit Q c0 t V hp.hc0 hV i))
  have hphysical := hbound θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical
    hR hH hholes hHR hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η C D hC hD hCD
    hη hCcap hDcap E hE Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst hξfirst hfirst
    χ₀ msecond hm hml hm2 Tsecond (sharpSupport s) hT hTcap hX hXcap hXupper hWupper hWinv hTupper
    n hret hKLcap hKRcap hTL hTR seed hseedC hseedD u huC huD Ds rows hDs hrows weight mass
    hmass hweight hDN hKLrows hKRrows hDartCap K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
  have hpaid (Dart : Id) (hDart : Dart∈artificialDivisors sActual C D hD.1)
      (hμ : (UniqueFactorizationMonoid.moebius Dart:ℂ)≠0) (χ ξ : RayCharacter) :
      budget Dart χ ξ≤(Z^loss*coeff)/(Dart.absNorm:ℝ) := by
    exact fixed_pair_paid U c s ha (zero_lt_one.trans_le hb) hunit η Q w t V hV p hp g
      C D hC hD hCD E hCcap hDcap hfirst n hret Dart
      (squarefree_of_moebius_ne_zero Dart hμ).ne_zero χ ξ
  have hsum := projector_majorant (artificialDivisors sActual C D hD.1)
    (Z^loss*coeff) budget hpaid
  have hZ0 := zero_lt_one.trans hZ
  have hKL0 : 0≤KL := Real.rpow_nonneg hZ0.le _
  have hKR0 : 0≤KR := Real.rpow_nonneg hZ0.le _
  have hpush := pushCost_upper Z Btail ε Cpush mass KL KR W hZ0 hε.le hCpush.le hmass
    hKL0 hKR0 hWblock.le hKLcap hKRcap hWupper
  let B0:=‖commonHeight sActual η t C D‖*referencePrefactor s η C D E Kfirst (Real.log 4)*
    Ckernel*windowMass (degree U) t^2
  have hB0 : 0≤B0 := mul_nonneg (mul_nonneg
    (mul_nonneg (norm_nonneg _) (referencePrefactor_nonneg s η C D E Kfirst (Real.log 4) hKfirst.le))
    hCkernel) (sq_nonneg _)
  have hpush0 : 0≤pushCost Cpush mass KL KR W ε :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have htotal : 0≤(Z^loss*coeff)*rayMass*artificialMass sActual C D hD.1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ0.le _) hcoeff) rayMass_nonneg)
      (artificialMass_nonneg sActual C D hD.1)
  calc
    _≤(B0*pushCost Cpush mass KL KR W ε)*
        (∑Dart∈artificialDivisors sActual C D hD.1,‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖*
          ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*budget Dart χ ξ) := by
      convert hphysical using 1 <;> (try dsimp only [B0,budget,left,right]) <;> ring
    _≤(B0*pushCost Cpush mass KL KR W ε)*
        ((Z^loss*coeff)*rayMass*artificialMass sActual C D hD.1) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hB0 hpush0)
    _≤(B0*((Z^loss*coeff)*rayMass*artificialMass sActual C D hD.1))*
        (mass*Cpush*(16:ℝ)^ε*Z^(5*Btail*ε)) := by
      convert mul_le_mul_of_nonneg_left hpush (mul_nonneg hB0 htotal) using 1 <;> ring
    _=_ := by
      dsimp only [B0,coeff,profileEnvelope]
      rw [unit_reference_prefactor s hunit η C D E Kfirst,Real.rpow_add hZ0]
      ring

end
end Candidate.Feedback.FourthPower.MixedFirstPaidPhysical
