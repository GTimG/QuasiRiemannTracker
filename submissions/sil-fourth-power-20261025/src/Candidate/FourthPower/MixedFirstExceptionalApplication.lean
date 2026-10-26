/- Copyright (c) 2026 Sil. Apache-2.0.
Actual exceptional component of the four-part first-source split.
The fixed pair supplies both child characters, and every structural
admission bound is derived from original geometric scale hypotheses.
-/
import Candidate.FourthPower.MixedFirstFourParts
import Candidate.FourthPower.MixedFirstExceptionalCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstExceptionalApplication
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentLattice
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalNormCap MixedOriginalTail
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstLiveSource MixedFirstAllocatedRemainders MixedFirstFourParts
open MixedFirstExceptionalNormalization MixedFirstExceptionalWindow MixedFirstExceptionalCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- This identity uses the exact B-dependent sourceNormCap from the
four-part split; the artificial seed and the outside W are unchanged. -/
theorem actual_component_identity (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G Gopp Dart Q : Id) (τ : Character)
    (t K W Tsec Z ξ : ℝ) (hW : 0≤W) (m : O) (χ₀ : RayCharacter) :
    components s ha hb cover G Dart τ t K W Tsec Z ξ Q m χ₀ 2/
      reference τ G Gopp (sourceVolume s) Z=
    exceptionalAllocation s ha hb cover τ χ₀ Q m Dart t ballProfile Z Tsec ξ G Gopp
      (fun B=>let live:=allocatedLiveSource s hb cover G B
        sourceNormCap live.P b live.T live.d) K W := by
  change allocatedExceptional s ha hb cover G Dart τ t K W Tsec Z ξ Q m χ₀/_=_
  rw [allocated_exceptional_norm_div s ha hb cover G Dart τ t K W Tsec Z ξ hW Q m χ₀]
  simp only [allocationSum,exceptionalAllocation,mul_div_assoc,Finset.sum_div]

def normExponent (Lscale Pexp εcap : ℝ) : ℝ := 2*Lscale+Pexp+εcap

def admissionExponent (Lscale Pexp εcap Bη BR BG BH M : ℝ) : ℝ :=
  max BH (max (Pexp+εcap) (Bη+BR+3*BG+8*Lscale+4*Pexp+M+6*εcap))

/-- Explicit numerical RHS. The fixed-Q/profile cost is originalFactor;
the first reference cost retains W^(7/3), all original prefixes and the
true modulus. In particular 1/N(Dart) has not been absorbed into Z. -/
def numericalCost (s : Source ι a b) (η : Character) (G Dart Q : Id)
    (J : ℕ) (control : Finset (ℕ×ℕ))
    (Bnorm ε δ εsum δalloc Ckernel A Csum Ccount Z K Cfirst ξfirst κ W t : ℝ) : ℝ :=
  ((Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*Z^(2*Bnorm*δ)*
    (Csum*Z^εsum/(Dart.absNorm:ℝ)))*
  (Ccount*(G.absNorm:ℝ)^δalloc*originalFactor s J control Q Z ε*
    Z^(referenceExponent s η K Z Cfirst ξfirst κ W))

/-- BOTH literal exceptional components of the actual fixed pair.
There are no pool/family conductor, row, count or energy-bound premises.
Only original geometric norm caps and the chosen cutoff parameters
remain. The right side uses the checked exact swapped presentation.
All controls and thresholds precede actual sources, ideals and heights. -/
theorem uniform_fixed_pair_components (N : ℕ)
    (α a b ε δ εsum δalloc εcap Lscale Pexp Bη BR BG BH M : ℝ)
    (hα : (2/3:ℝ)≤α) (hα4 : α<4/5) (ha : 0<a) (hb : 0≤b)
    (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1)
    (hεsum : 0<εsum) (hδalloc : 0<δalloc) (hεcap : 0<εcap)
    (hL : 0≤Lscale) (hPexp : 0≤Pexp) (hBH : 0≤BH) (hM : 0≤M) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃A Csum Ccount : ℝ,0<A ∧ 0<Csum ∧ 0<Ccount ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,
      Fintype.card ι≤N → s.X₁≤Z^Lscale → s.X₂≤Z^Lscale →
      s.Y₁≤Z^Lscale → s.Y₂≤Z^Lscale → (∏i,s.P i)≤Z^Pexp →
      (s.R.absNorm:ℝ)≤Z^BR → (s.Fhole.absNorm:ℝ)≤Z^BH →
      ∀(η : Character)(C D : Id)(hC : Supported C)(hD : Supported D),
      CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      (η.modulus.absNorm:ℝ)≤Z^Bη → (C.absNorm:ℝ)≤Z^BG → (D.absNorm:ℝ)≤Z^BG →
      ∀(E : Finset (CommonIndex C D))(χ ξ : RayCharacter),
      ∀F : FixedPair η C D hC E χ ξ,∀(K Tfirst Cfirst ξfirst κ W : ℝ),
      0<K → 0<W → 1≤Cfirst → 0≤ξfirst →
      Tfirst≤Cfirst*firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K (sourceVolume s) →
      ∀(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀Dart : Id,Squarefree Dart → Dart≠0 →
      ∀(tleft tright Tsecond ξsecond : ℝ),0≤Tsecond → Tsecond≤Z^(M-ξsecond/2) →
      ∀n : ℤ,Retained (frequencyRadius Tfirst Z ξfirst) n →
      (components s ha hb cover C Dart F.left tleft
        (nominalChildScale C D E K (sourceVolume s) Z κ n) W Tsecond Z ξsecond Q m χ₀ 2/
        reference F.left C D (sourceVolume s) Z≤
        numericalCost s η C Dart Q J control (normExponent Lscale Pexp εcap)
          ε δ εsum δalloc Ckernel A Csum Ccount Z K Cfirst ξfirst κ W tleft) ∧
      (components s ha hb cover D Dart F.right tright
        (nominalChildScale D C (swapSubset C D E) K (sourceVolume s) Z κ n)
          W Tsecond Z ξsecond Q m χ₀ 2/reference F.right D C (sourceVolume s) Z≤
        numericalCost s η D Dart Q J control (normExponent Lscale Pexp εcap)
          ε δ εsum δalloc Ckernel A Csum Ccount Z K Cfirst ξfirst κ W tright) := by
  let Bnorm := normExponent Lscale Pexp εcap
  let Bcap := admissionExponent Lscale Pexp εcap Bη BR BG BH M
  have hBnorm : 0≤Bnorm := by dsimp only [Bnorm,normExponent];linarith
  have hBcap : 0≤Bcap := hBH.trans (le_max_left _ _)
  have hmarkExponent : Pexp+εcap≤Bcap :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hfamilyExponent : Bη+BR+3*BG+8*Lscale+4*Pexp+M+6*εcap≤Bcap :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨J,control,h00,hkernel⟩ := uniform_actual_allocation_reference N
    α Bcap a b ε δ Bnorm M 1 εsum δalloc hα hα4 hBcap ha hb hε hδ hgap
      hBnorm hM zero_lt_one hεsum hδalloc
  obtain ⟨Ckernel,hCkernel,hQ⟩ := hkernel ballProfile
  refine ⟨J,control,h00,Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,Csum,Ccount,hA,hCsum,hCcount,hpoint⟩ := hQ Q hQ0 hQt hQ72
  have htwo : ∀ᶠZ : ℝ in atTop,(2:ℝ)^N≤Z^εcap :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hεcap)) ((2:ℝ)^N)
  refine ⟨A,Csum,Ccount,hA,hCsum,hCcount,?_⟩
  filter_upwards [hpoint,htwo,
    eventually_allocated_caps N b Lscale Pexp εcap 0 BR BG M hb hεcap,
    eventually_fixed_pair_family_caps N b Lscale Pexp εcap Bη BR BG M hb hεcap]
    with Z hpoint htwo hnorms hfamilies
  obtain ⟨hZ,hpoint⟩ := hpoint
  refine ⟨hZ,?_⟩
  intro ι instι s cover hcard hX₁ hX₂ hY₁ hY₂ hP hR hF η C D hC hD hCD
    hη hCcap hDcap E χ ξ F K Tfirst Cfirst ξfirst κ W hK hW hCfirst hξfirst hfirst
    χ₀ m hm hml hm2 Dart hDart hDart0 tleft tright Tsecond ξsecond hT hTcap n hn
  have hz := zero_lt_one.trans hZ
  have hFcap : (s.Fhole.absNorm:ℝ)≤Z^Bcap := hF.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (le_max_left _ _))
  have hmarked : (∏i,2*s.P i)≤Z^Bcap := by
    calc
      _=(2:ℝ)^Fintype.card ι*(∏i,s.P i) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      _≤(2:ℝ)^N*Z^Pexp :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard) hP
          (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))) (by positivity)
      _≤Z^εcap*Z^Pexp := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hz.le _)
      _=Z^(Pexp+εcap) := by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^Bcap := Real.rpow_le_rpow_of_exponent_le hZ.le hmarkExponent
  have hradius : frequencyRadius Tsecond Z ξsecond≤Z^M := by
    unfold frequencyRadius
    calc
      _≤Z^(M-ξsecond/2)*Z^(ξsecond/2) :=
        mul_le_mul_of_nonneg_right hTcap (Real.rpow_nonneg hz.le _)
      _=Z^M := by rw [←Real.rpow_add hz];congr 1;ring
  have hradius0 : 0≤frequencyRadius Tsecond Z ξsecond :=
    mul_nonneg hT (Real.rpow_nonneg hz.le _)
  have hside (G Gopp : Id) (hG : Supported G) (hGopp : Supported Gopp)
      (hGGopp : CompletedGauss.primeSupport G=CompletedGauss.primeSupport Gopp)
      (Eside : Finset (CommonIndex G Gopp)) (τ : Character) (t : ℝ)
      (hτ : τ=F.left ∨ τ=F.right) (hGcap : (G.absNorm:ℝ)≤Z^BG)
      (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex G Gopp=>P.val) Eside*
          activeConductor G Gopp})
      (hsector : Tfirst≤Cfirst*firstNominalScale G Gopp
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex G Gopp=>P.val) Eside})
          K (sourceVolume s)) :
      components s ha hb cover G Dart τ t
        (nominalChildScale G Gopp Eside K (sourceVolume s) Z κ n)
        W Tsecond Z ξsecond Q m χ₀ 2/reference τ G Gopp (sourceVolume s) Z≤
        numericalCost s η G Dart Q J control Bnorm ε δ εsum δalloc
          Ckernel A Csum Ccount Z K Cfirst ξfirst κ W t := by
    rw [actual_component_identity s ha hb cover G Gopp Dart Q τ t
      (nominalChildScale G Gopp Eside K (sourceVolume s) Z κ n)
      W Tsecond Z ξsecond hW.le m χ₀]
    apply hpoint ι s cover hcard hFcap hmarked η τ G Gopp hG hGopp hGGopp Eside
      K Tfirst Cfirst ξfirst κ W hK hW hCfirst hξfirst hmod hsector
      χ₀ m hm hml hm2 Dart hDart hDart0 t Tsecond ξsecond
      (fun B=>let live:=allocatedLiveSource s hb cover G B
        sourceNormCap live.P b live.T live.d) hT
      (by simpa only [one_mul] using hradius) ?_ n hn
    intro B _hfrozen
    have hc := hnorms.2 ι a s cover hcard hX₁ hX₂ hY₁ hY₂ hP hR G hGcap B
    have hf := hfamilies.2 ι a s cover hcard hX₁ hX₂ hY₁ hY₂ hP hR
      η C D hC hη hCcap E χ ξ F G hGcap B τ (frequencyRadius Tsecond Z ξsecond)
      hτ hradius0 hradius
    exact ⟨hc.2.1,hc.1,hf.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hfamilyExponent)⟩
  refine ⟨hside C D hC hD hCD E F.left tleft (Or.inl rfl) hCcap F.left_modulus hfirst,?_⟩
  apply hside D C hD hC hCD.symm (swapSubset C D E) F.right tright
    (Or.inr rfl) hDcap (right_modulus η C D hC E χ ξ F)
  simpa only [swapSubset_generator,nominal_swap] using hfirst

end
end Candidate.FourthPower.MixedFirstExceptionalApplication
