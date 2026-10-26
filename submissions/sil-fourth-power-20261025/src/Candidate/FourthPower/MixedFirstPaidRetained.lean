/- Copyright (c) 2026 Sil. Apache-2.0.
Actual paid selected first retained energy. The source support and common
labels are fixed before the selected product. Only numerical geometry and
the original canonical profile data are premises; all energy estimates
are supplied by uniform_paid_physical. Parent checks Lean.
-/
import Candidate.FourthPower.MixedFirstPaidPhysical
import Candidate.FourthPower.MixedFirstRetainedFixed
import Candidate.FourthPower.MixedOriginalCoprimality
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstPaidRetained
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ConcreteTraceCRT RayFourExpansion ActualEisensteinCubic
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectorTransform
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstSectors
open CenteredMomentNaturalFixedRaySource CenteredMomentFirstTailAggregate
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedHeightEnvelope
open MixedFirstActualNonexceptional MixedFirstFullBudget MixedFirstLiveSource
open MixedFirstExceptionalNormalization MixedFirstExceptionalApplication
open MixedFirstAvoidance MixedFirstPhysicalApplication MixedFirstPhysicalBudget
open MixedFirstIntegratedWindows MixedFirstPaidCosts MixedFirstPaidPhysical
open MixedFirstCommonSum MixedFirstRetainedFixed MixedFirstGeometricCaps
open MixedOriginalCoprimality MixedSupplierSource ReferencePrimeEnclosure MixedCompletedRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- One provenance condition, before all common labels. Actual suppliers
have u=f*seed and puncture R*f, so need not have u dividing R alone. -/
theorem avoidance_on_labels (s : Source ι a b) (ha : 0<a) (seed u : Id)
    (hseed : Squarefree seed) (hu : u∣s.R*seed)
    (p : Labels (avoidSource s u) ha seed) :
    seed∣p.val.1 ∧ seed∣p.val.2 ∧ u∣s.R*p.val.1 ∧ u∣s.R*p.val.2 := by
  have hs := active_common_seed (sourceColumns (avoidSource s u))
    (sourceCoefficient (avoidSource s u) ha seed) seed hseed
    (fun I hI=>source_coefficient_seed (avoidSource s u) ha seed I hI) p
  exact ⟨hs.1,hs.2,hu.trans (mul_dvd_mul_left s.R hs.1),
    hu.trans (mul_dvd_mul_left s.R hs.2)⟩

theorem supplier_global_avoidance (R f seed u : Id) (hu : u=f*seed) :
    u∣(R*f)*seed := supplier_dvd_puncture R f seed u seed hu dvd_rfl

/-- Literal finite-band geometry. These are scalar/cutoff/support caps,
not bounds for any source, moment, block, or energy. The checked
uniform_actual_cutoffs supplies the child fields using annular inclusion. -/
structure BandGeometry (s : Source ι a b) (ha : 0<a) (seed : Id)
    (K Z ξ κ W Tsecond H Btail Bfrequency : ℝ) : Prop where
  radius : ∀p : Labels s ha seed,∀E : Finset (CommonIndex p.val.1 p.val.2),
    firstRadius s p.val.1 p.val.2 E K Z ξ≤Z^Bfrequency
  artificial : ∀p : Labels s ha seed,
    ∀Dart∈artificialDivisors s p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).2.1,
      (UniqueFactorizationMonoid.moebius Dart:ℂ)≠0→(Dart.absNorm:ℝ)≤Z^Btail
  children : ∀p : Labels s ha seed,∀E∈inactiveSubsets p.val.1 p.val.2,
    ∀n : Blocks (effectiveScale p.val.1 p.val.2 E K)
      (firstRadius s p.val.1 p.val.2 E K Z ξ) (H/p.val.1.absNorm) (H/p.val.2.absNorm),
    let KL:=nominalChildScale p.val.1 p.val.2 E K (sourceVolume s) Z κ (n 1)
    let KR:=nominalChildScale p.val.2 p.val.1 (swapSubset p.val.1 p.val.2 E)
      K (sourceVolume s) Z κ (n 1)
    KL≤Z^Btail ∧ KR≤Z^Btail ∧
      sharpSupport s^2/(16*KL*W^4)≤Tsecond ∧ sharpSupport s^2/(16*KR*W^4)≤Tsecond ∧
    ∀z∈fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i=>(n i:ℤ)),
      (Ideal.absNorm (Ideal.span {z}):ℝ)≤KL ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤KR

def retainedFactor (U : Controls) (c : Constants) (s : Source ι a b)
    (η : Character) (Q : Id) (c0 t V K mass Cpush Ckernel ε : ℝ) : ℝ :=
  (4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*Ckernel*
    (mass*Cpush*(16:ℝ)^ε)*profileEnvelope U c s Q c0 t V*rayMass

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Complete retained aggregate, using the actual paid block theorem.
The only common-label hypotheses are literal numerical BandGeometry.
The full seed norm is saved after the genuine/artificial/dyadic sums. -/
theorem uniform_paid_retained
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BG BH Bsource Bη Pexp Mgeom Btail
      ε δ lo hi ξsecond saving Bfrequency εsum : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hMcap0 : 0<Mcap)
    (hL : 0≤L) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBG : 0≤BG) (hBH : 0≤BH) (hBsource : 0≤Bsource)
    (hPexp : 0≤Pexp) (hMgeom : 0≤Mgeom) (hBtail : 0≤Btail) (hBGtail : BG≤Btail)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hgap : (7/10:ℝ)+2*δ<1) (hξsecond : 0<ξsecond)
    (hMcap : Mgeom+(Bη+BG+ε)+Bsource+ε≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hfrequency : 0≤Bfrequency) (hεsum : 0<εsum)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃U : Controls,∃Cpush Ckernel Csum : ℝ,0<Cpush ∧ 0≤Ckernel ∧ 0<Csum ∧
    ∀η₀ : Character,Q≤η₀.modulus→∃c : Constants,
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t R₀ s→
      s.d=(1,1)→(s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      sourceNormCap s.P b s.T s.d≤Z^Bsource→poolCap s≤Z^Btail→
      (∏i,s.P i)≤Z^Pexp→(s.Fhole.absNorm:ℝ)≤Z^BH→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀(K ξfirst κpad W Tsecond H : ℝ),0<K→0<W→0≤ξfirst→
      0≤Tsecond→Tsecond≤Z^(Mgeom-ξsecond)→Tsecond≤Z^Btail→
      1≤sharpSupport s→sharpSupport s≤Z^Btail→W≤Z^Btail→W⁻¹≤Z^Btail→
      0<H→sourceNormCap s.P b s.T s.d≤H→H≤Z^BG→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀seed : Id,Squarefree seed→seed≠0→∀u : Id,u∣s.R*seed→
    let sActual:=avoidSource s u
    BandGeometry sActual ha seed K Z ξfirst κpad W Tsecond H Btail Bfrequency→
    ∀Ds : Finset Id,(∀F∈Ds,Supported F)→∀(weight : Id→ℝ)(mass : ℝ),0≤mass→
      (∀F∈Ds,0≤weight F∧weight F≤mass)→(∀F∈Ds,(F.absNorm:ℝ)≤2*W)→
    ∀Rexp Praw Sraw dsel lref c0 omega sigma loss BX : ℝ,
    let p0 : Parameters :=
      { Z:=Z,Kfirst:=K,Tfirst:=0,Cfirst:=1,ξfirst:=ξfirst,κpad:=κpad,W:=W,
        ε:=ε,δ:=δ,Bnorm:=normExponent L Pexp ε,BG:=BG,BX:=BX,R:=Rexp,P:=Praw,S:=Sraw,
        d:=dsel,l:=lref,c0:=c0,omega:=omega,sigma:=sigma,loss:=loss,saving:=saving }
    Gates p0→SourceGeometry p0 s η w→
    ‖∑F∈Ds,((weight F/W:ℝ):ℂ)*retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t
      (sourceColumns sActual) (selectedCoefficient sActual ha seed F) Φ K (sourceVolume s) Z ξfirst‖/
        sourceVolume s≤
      Csum*retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε*
        Z^(loss+5*Btail*ε+εsum)/(seed.absNorm:ℝ) := by
  obtain ⟨U,Cpush,Ckernel,hCpush,hCkernel,hpaid⟩ := uniform_paid_physical
    (ι:=ι) M Hray hHray Φ 0 N Holes hcard Wslot a b Mcap L Lslot Lcap Cap
    BR BG BH Bsource Bη Pexp Mgeom Btail ε δ lo hi ξsecond saving
    hWs hW ha haUpper hb hMcap0 hL hLslot hLcap hCap hBR hBG hBH hBsource hPexp
    hMgeom hBtail hBGtail hCapb hLordinary hε hδ hgap hξsecond hMcap hβ Q hQt hQ72 hQM
  obtain ⟨Csum,hCsum,hcommon⟩ := uniform_common_artificial_band_mass
    BG Bfrequency Btail 1 εsum hBG hfrequency hBtail (by norm_num) hεsum
  refine ⟨U,Cpush,Ckernel,Csum,hCpush,hCkernel,hCsum,?_⟩
  intro η₀ hη₀
  obtain ⟨c,hpaid⟩ := hpaid η₀ hη₀
  refine ⟨c,?_⟩
  filter_upwards [hpaid,hcommon] with Z hz hm
  obtain ⟨hZ,hpaid⟩ := hz
  refine ⟨hZ,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit hR hHholes hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η hη K ξfirst κpad W Tsecond H hK hWblock hξ
    hT hTcap hTupper hX hXupper hWupper hWinv hH hsourceH hHcap
    χ₀ msecond hmsecond hml hm2 seed hseed hseed0 u hu sActual hgeometry
    Ds hDs weight mass hmass hweight hDN Rexp Praw Sraw dsel lref c0 omega sigma loss BX p0 hp0 hg0
  let A:=retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε
  have hA : 0≤A := by
    have hprofiles := profileEnvelope_nonneg U c s ha hunit Q c0 t V hp0.hc0 hV
    have hpresentation := fixedPresentationCost_pos.le
    have hrays := rayMass_nonneg
    dsimp only [A,retainedFactor]
    positivity
  let radius:=fun (p : Labels sActual ha seed) (E : Finset (CommonIndex p.val.1 p.val.2))=>
    firstRadius sActual p.val.1 p.val.2 E K Z ξfirst
  let divisors:=fun (p : Labels sActual ha seed) (_E : Finset (CommonIndex p.val.1 p.val.2))=>
    artificialDivisors sActual p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).2.1
  have hmasssum := hm.2 ι a b sActual ha seed hseed hseed0 K H hK hH hsourceH hHcap
    radius (fun p E=>by simpa only [one_mul] using hgeometry.radius p E) divisors
    (fun p E D hD hμ=>hgeometry.artificial p D hD hμ)
  let term:=fun (p : Labels sActual ha seed) (E : Finset (CommonIndex p.val.1 p.val.2))
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm))=>
    physicalAverage sActual ha seed η t p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).1
      (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).2
      E (fixedRows (radius p E) (fun i=>(n i:ℤ))) Ds weight W Φ K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
  have hpoint (p : Labels sActual ha seed) (E : Finset (CommonIndex p.val.1 p.val.2))
      (hE : E∈inactiveSubsets p.val.1 p.val.2)
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm)) :
      ‖term p E n‖/sourceVolume s≤
        (A*Z^(loss+5*Btail*ε))*commonWeight p.val.1 p.val.2 E*
          artificialMass sActual p.val.1 p.val.2
            (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).2.1 := by
    have hs := commonLabels_supported
      (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p
    have hCD := (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2
    have hnorm := commonLabel_norm_bounds (sourceColumns sActual) (sourceCoefficient sActual ha seed) H
      (fun I _ hI=>(original_coefficient_cap sActual ha seed I hI).2.trans hsourceH)
      p.val.1 p.val.2 p.property
    have havoid := avoidance_on_labels s ha seed u hseed hu p
    let Tfirst:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (sourceVolume s)
    have hfirst : Tfirst≤1*firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex p.val.1 p.val.2=>P.val) E})
        K (sourceVolume s) := by
      simp only [Tfirst,one_mul,primeSubsetGenerator,span_idealGenerator,le_refl]
    have hret : Retained (frequencyRadius Tfirst Z ξfirst) (n 1) :=
      block_retained _ _ _ _ n
    obtain ⟨hKL,hKR,hTL,hTR,hrows⟩ := hgeometry.children p E hE n
    have hp1 : Gates {p0 with Tfirst := Tfirst} :=
      ⟨hp0.hZ,hp0.hK,hp0.hW,hp0.hc0,hp0.hCfirst,hp0.hξ,hp0.hε,hp0.hδ,
        hp0.hS,hp0.hd,hp0.mixed,hp0.native,hp0.reference,hp0.Wlower,hp0.Wupper,
        hp0.frequency,hp0.zero_loss,hp0.native_loss,hp0.exceptional_loss,hp0.tail_loss⟩
    have hg1 : SourceGeometry {p0 with Tfirst := Tfirst} s η w :=
      ⟨hg0.volume,hg0.width,hg0.length,hg0.support,hg0.slots⟩
    have hbnd := hpaid θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit
      hR hHholes hholes hHR hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η
      p.val.1 p.val.2 hs.1 hs.2 hCD hη (hnorm.1.trans hHcap) (hnorm.2.trans hHcap)
      E hE K Tfirst 1 ξfirst κpad W hK hWblock (by norm_num) hξ hfirst
      χ₀ msecond hmsecond hml hm2 Tsecond hT hTcap hX le_rfl hXupper hWupper hWinv hTupper
      (n 1) hret hKL hKR hTL hTR seed havoid.1 havoid.2.1 u havoid.2.2.1 havoid.2.2.2
      Ds (fixedRows (radius p E) (fun i=>(n i:ℤ))) hDs
      (fixedRows_nonzero _ _) weight mass hmass hweight hDN
      (fun z hz=>(hrows z hz).1) (fun z hz=>(hrows z hz).2)
      (hgeometry.artificial p)
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
      (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
      Rexp Praw Sraw dsel lref c0 omega sigma loss BX hp1 hg1
    have hheight : ‖commonHeight sActual η t p.val.1 p.val.2‖≤1 := by
      rw [commonHeight,norm_mul,norm_star]
      exact (mul_le_mul (rowWeight_norm_le_one η (fixedBadMask*idealGenerator sActual.R)
        1 1 t p.val.1 hs.1.1) (rowWeight_norm_le_one η (fixedBadMask*idealGenerator sActual.R)
        1 1 t p.val.2 hs.2.1) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have hnonneg : 0≤(A*Z^(loss+5*Btail*ε))*commonWeight p.val.1 p.val.2 E*
        artificialMass sActual p.val.1 p.val.2 hs.2.1 :=
      mul_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg (by linarith [hZ]) _))
        (common_weight_nonneg _ _ _)) (artificialMass_nonneg _ _ _ _)
    apply (show ‖term p E n‖/sourceVolume s≤‖commonHeight sActual η t p.val.1 p.val.2‖*
      ((A*Z^(loss+5*Btail*ε))*commonWeight p.val.1 p.val.2 E*
        artificialMass sActual p.val.1 p.val.2 hs.2.1) from by
      convert hbnd using 1 <;> simp only [pow_zero,one_mul,term,A,retainedFactor] <;> ring).trans
    exact mul_le_of_le_one_left hnonneg hheight
  change ‖∑F∈Ds,((weight F/W:ℝ):ℂ)*retainedEnergy η
    (fixedBadMask*idealGenerator sActual.R) 1 t (sourceColumns sActual)
    (selectedCoefficient sActual ha seed F) Φ K (sourceVolume sActual) Z ξfirst‖/
    sourceVolume s≤_
  rw [selected_retained_average sActual ha seed η t Φ K Z ξfirst H hK hsourceH Ds weight W]
  change ‖∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
    ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
      (H/p.val.1.absNorm) (H/p.val.2.absNorm),term p E n‖/sourceVolume s≤_
  have htri : ‖∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),term p E n‖≤
      ∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (H/p.val.1.absNorm) (H/p.val.2.absNorm),‖term p E n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun E hE=>norm_sum_le _ _)
  apply (div_le_div_of_nonneg_right htri (sourceVolume_pos s).le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),
      (A*Z^(loss+5*Btail*ε))*commonWeight p.val.1 p.val.2 E*
        artificialMass sActual p.val.1 p.val.2
          (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).2.1 :=
      Finset.sum_le_sum (fun p _=>Finset.sum_le_sum (fun E hE=>Finset.sum_le_sum (fun n _=>hpoint p E hE n)))
    _=(A*Z^(loss+5*Btail*ε))*(∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),∑Dart∈divisors p E,
      commonWeight p.val.1 p.val.2 E*(‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖/(Dart.absNorm:ℝ))) := by
      simp only [artificialMass,divisors,Finset.mul_sum,mul_assoc]
    _≤(A*Z^(loss+5*Btail*ε))*(Csum*Z^εsum/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hmasssum (mul_nonneg hA (Real.rpow_nonneg (by linarith [hZ]) _))
    _=_ := by
      have he : Z^(loss+5*Btail*ε+εsum)=Z^(loss+5*Btail*ε)*Z^εsum := by
        rw [Real.rpow_add (zero_lt_one.trans hZ)]
      rw [he]
      dsimp only [A]
      ring

end
end Candidate.FourthPower.MixedFirstPaidRetained
