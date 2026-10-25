/- Copyright (c) 2026 Sil. Apache-2.0.
The actual selected first physical block, with all finite projectors and
the literal prefix/reference normalization.
-/
import Candidate.Feedback.FourthPower.MixedFirstPhysicalApplication
import Candidate.Feedback.FourthPower.MixedFirstIntegratedWindows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedFirstPhysicalBudget
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
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalNormCap MixedOriginalTail
open MixedOriginalSecondZero MixedFirstLiveSource MixedFirstFourParts
open MixedFirstNonexceptionalAllocation MixedFirstReferencePair MixedFirstInactiveConductor
open MixedFirstExceptionalNormalization MixedFirstExceptionalApplication MixedInnerExceptionalBlock
open MixedFirstFullBudget MixedFirstAveragedWindow MixedHeightEnvelope MixedFirstAvoidance
open MixedFirstIntegratedWindows MixedFirstPhysicalApplication MixedFirstTwistedReference
open ReferencePrimeEnclosure MixedCompletedRows QuadraticInitialBound
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def windowMass (J : ℕ) (t : ℝ) : ℝ := heightEnvelope t^J*profileMoment J

theorem windowMass_nonneg (J : ℕ) (t : ℝ) : 0≤windowMass J t :=
  mul_nonneg (pow_nonneg (heightEnvelope_pos t).le _) (profileMoment_nonneg J)

/-- No prefix norm is hidden in a Z-dependent constant. -/
def referencePrefactor (s : Source ι a b) (η : Character) (C D : Id)
    (E : Finset (CommonIndex C D)) (K M : ℝ) : ℝ :=
  ‖inactiveWeight C D E‖*(Real.exp M/(a^2/pairNorm s.d))*fixedPresentationCost*K*
    (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm

theorem referencePrefactor_nonneg (s : Source ι a b) (η : Character) (C D : Id)
    (E : Finset (CommonIndex C D)) (K M : ℝ) (hK : 0≤K) :
    0≤referencePrefactor s η C D E K M := by
  have := fixedPresentationCost_pos.le
  have := (pairNorm_pos s.hd.1 s.hd.2).le
  unfold referencePrefactor
  positivity

def physicalAverage (s : Source ι a b) (ha : 0<a) (seed : Id) (η : Character)
    (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (Ds : Finset Id)
    (weight : Id→ℝ) (W : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  commonHeight s η t C D*∑F∈Ds,((weight F/W:ℝ):ℂ)*
    block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (selectedCoefficient s ha seed F) C D hC hD E rows Φ (fun _=>logAnnulus) K K₀ H₀ A₀ B₀

/-- Nonzero AVERAGED physical data produce an actual selected member.
There is no inference to the nonvanishing of an untwisted block. -/
private theorem actual_member (s : Source ι a b) (ha : 0<a) (seed : Id) (η : Character)
    (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (Ds : Finset Id)
    (weight : Id→ℝ) (W : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ)
    (hne : physicalAverage s ha seed η t C D hC hD E rows Ds weight W Φ K K₀ H₀ A₀ B₀≠0) :
    ∃F∈Ds,block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (selectedCoefficient s ha seed F) C D hC hD E rows Φ (fun _=>logAnnulus) K K₀ H₀ A₀ B₀≠0 := by
  have hs := (mul_ne_zero_iff.mp hne).2
  obtain ⟨F,hF,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact ⟨F,hF,(mul_ne_zero_iff.mp hterm).2⟩

/-- Pure reference arithmetic for every one of the sixteen component
pairs, normalized using one ACTUAL nonzero selected physical block. -/
private theorem normalize_window_cost (s : Source ι a b) (ha : 0<a)
    (seed Fsel : Id) (η : Character) (t : ℝ) (C D : Id)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (E : Finset (CommonIndex C D)) (χ ξ : RayCharacter) (P : FixedPair η C D hC E χ ξ)
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ Z : ℝ)
    (hK : 0<K) (hA₀ : 0<A₀) (hB₀ : 0<B₀) (hZ : 1<Z)
    (hn : block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (selectedCoefficient s ha seed Fsel) C D hC hD E rows Φ (fun _=>logAnnulus) K K₀ H₀ A₀ B₀≠0)
    (J : ℕ) (left right : Fin 4→ℝ) (hl : ∀i,0≤left i) (hr : ∀j,0≤right j) :
    (‖scalar C D hC E K A₀ B₀‖/sourceVolume s)*
      (∑i : Fin 4,∑j : Fin 4,windowBudget J t (left i)*windowBudget J t (right j))≤
    referencePrefactor s η C D E K (Real.log 4)*windowMass J t^2*
      ∑i : Fin 4,∑j : Fin 4,
        Real.sqrt ((left i/reference P.left C D (sourceVolume s) Z)*
          (right j/reference P.right D C (sourceVolume s) Z)) := by
  have hlref := MixedFirstFullBudget.reference_pos s P.left C D hC.1 Z (zero_lt_one.trans hZ)
  have hrref := MixedFirstFullBudget.reference_pos s P.right D C hD.1 Z (zero_lt_one.trans hZ)
  have hpref := referencePrefactor_nonneg s η C D E K (Real.log 4) hK.le
  have hwin : ∀i : Fin 4,∀y : ℝ,logAnnulus y≠0→|y|≤Real.log 4 := by
    intro i y hy
    have hy' := logAnnulus_support hy
    exact abs_le.mpr ⟨hy'.1,hy'.2.trans (Real.log_nonneg (by norm_num))⟩
  have hpair (i j : Fin 4) :
      (‖scalar C D hC E K A₀ B₀‖/sourceVolume s)*
        (windowBudget J t (left i)*windowBudget J t (right j))≤
      referencePrefactor s η C D E K (Real.log 4)*windowMass J t^2*
        Real.sqrt ((left i/reference P.left C D (sourceVolume s) Z)*
          (right j/reference P.right D C (sourceVolume s) Z)) := by
    have hb := twisted_source_reference_pair s ha seed (selectedCoefficient s ha seed Fsel)
      (selected_support s ha seed Fsel) η (fixedBadMask*idealGenerator s.R) 1 t
      C D hC hD hCD E χ ξ P rows Φ (fun _=>logAnnulus)
      K K₀ H₀ A₀ B₀ (Real.log 4) Z
      (left i/reference P.left C D (sourceVolume s) Z)
      (right j/reference P.right D C (sourceVolume s) Z)
      hK hA₀ hB₀ hZ (div_nonneg (hl i) hlref.le) (div_nonneg (hr j) hrref.le) hwin hn
    change (‖scalar C D hC E K A₀ B₀‖/sourceVolume s)*
      Real.sqrt ((reference P.left C D (sourceVolume s) Z*
        (left i/reference P.left C D (sourceVolume s) Z))*
        (reference P.right D C (sourceVolume s) Z*
        (right j/reference P.right D C (sourceVolume s) Z)))≤
      referencePrefactor s η C D E K (Real.log 4)*_ at hb
    rw [mul_div_cancel₀ _ hlref.ne',mul_div_cancel₀ _ hrref.ne'] at hb
    have he : windowBudget J t (left i)*windowBudget J t (right j)=
        Real.sqrt (left i*right j)*windowMass J t^2 := by
      rw [Real.sqrt_mul (hl i)]
      unfold windowBudget windowMass
      ring
    rw [he]
    convert mul_le_mul_of_nonneg_right hb (sq_nonneg (windowMass J t)) using 1 <;> ring
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hpair i j))

private theorem scaled_norm_sum {α : Type*} (S : Finset α)
    (c f : α→ℂ) (r : ℝ) (hr : 0≤r) :
    r*‖∑i∈S,c i*f i‖≤∑i∈S,‖c i‖*(r*‖f i‖) := by
  apply (mul_le_mul_of_nonneg_left (norm_sum_le S (fun i=>c i*f i)) hr).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_mul]
  ring

private theorem projected_norm_bound (Ls : Finset Id) (ρ : ℂ) (hρ : ‖ρ‖≤1)
    (ray : RayCharacter→RayCharacter→ℂ) (matrix : Id→RayCharacter→RayCharacter→ℂ)
    (r A : ℝ) (hr : 0≤r) (hA : 0≤A) (B : Id→RayCharacter→RayCharacter→ℝ)
    (hB : ∀L χ ξ,0≤B L χ ξ)
    (hb : ∀L∈Ls,(UniqueFactorizationMonoid.moebius L:ℂ)≠0→∀χ ξ,
      r*‖matrix L χ ξ‖≤A*B L χ ξ) :
    r*‖∑L∈Ls,(UniqueFactorizationMonoid.moebius L:ℂ)*ρ*
      ∑χ : RayCharacter,∑ξ : RayCharacter,ray χ ξ*matrix L χ ξ‖≤
      A*∑L∈Ls,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
        ∑χ : RayCharacter,∑ξ : RayCharacter,‖ray χ ξ‖*B L χ ξ := by
  have hi (L : Id) (hL : L∈Ls) (hμ : (UniqueFactorizationMonoid.moebius L:ℂ)≠0) :
      r*‖∑χ : RayCharacter,∑ξ : RayCharacter,ray χ ξ*matrix L χ ξ‖≤
        A*∑χ : RayCharacter,∑ξ : RayCharacter,‖ray χ ξ‖*B L χ ξ := by
    calc
      _≤∑χ : RayCharacter,r*‖∑ξ : RayCharacter,ray χ ξ*matrix L χ ξ‖ := by
        simpa only [Finset.mul_sum] using
          mul_le_mul_of_nonneg_left (norm_sum_le Finset.univ
            (fun χ=>∑ξ : RayCharacter,ray χ ξ*matrix L χ ξ)) hr
      _≤∑χ : RayCharacter,∑ξ : RayCharacter,‖ray χ ξ‖*(r*‖matrix L χ ξ‖) :=
        Finset.sum_le_sum (fun χ _=>scaled_norm_sum Finset.univ (ray χ) (matrix L χ) r hr)
      _≤∑χ : RayCharacter,∑ξ : RayCharacter,‖ray χ ξ‖*(A*B L χ ξ) :=
        Finset.sum_le_sum (fun χ _=>Finset.sum_le_sum (fun ξ _=>
          mul_le_mul_of_nonneg_left (hb L hL hμ χ ξ) (norm_nonneg _)))
      _=_ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro χ hχ
                apply Finset.sum_congr rfl; intro ξ hξ; ring
  calc
    _≤∑L∈Ls,‖(UniqueFactorizationMonoid.moebius L:ℂ)*ρ‖*
        (r*‖∑χ : RayCharacter,∑ξ : RayCharacter,ray χ ξ*matrix L χ ξ‖) :=
      scaled_norm_sum Ls _ _ r hr
    _≤∑L∈Ls,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
        (A*∑χ : RayCharacter,∑ξ : RayCharacter,‖ray χ ξ‖*B L χ ξ) := by
      apply Finset.sum_le_sum
      intro L hL
      by_cases hμ : (UniqueFactorizationMonoid.moebius L:ℂ)=0
      · simp only [hμ,zero_mul,norm_zero,le_refl]
      · have hm : ‖(UniqueFactorizationMonoid.moebius L:ℂ)*ρ‖≤
            ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖ := by
          simpa only [norm_mul,mul_one] using
            mul_le_mul_of_nonneg_left hρ (norm_nonneg (UniqueFactorizationMonoid.moebius L:ℂ))
        exact mul_le_mul hm (hi L hL hμ) (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _)
    _=_ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L hL; ring

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Actual E1 quantitative endpoint. The constants come directly from
uniform_integrated_windows. All premises below concern the original
canonical source, exact source avoidance, and numerical physical geometry;
there is no moment, energy, Fourier-window or nonzero-block premise.
The actual zero-average case is handled separately. -/
theorem uniform_physical_budget
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
    ∀(Tsecond X : ℝ),0≤Tsecond→Tsecond≤Z^(Mgeom-ξsecond)→
      1≤X→(2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d≤X→
      X≤Z^Btail→W≤Z^Btail→W⁻¹≤Z^Btail→Tsecond≤Z^Btail→
    ∀n : ℤ,Retained (frequencyRadius Tfirst Z ξfirst) n→
    let KL:=nominalChildScale C D E Kfirst (sourceVolume s) Z κpad n
    let KR:=nominalChildScale D C (swapSubset C D E) Kfirst (sourceVolume s) Z κpad n
    KL≤Z^Btail→KR≤Z^Btail→X^2/(16*KL*W^4)≤Tsecond→X^2/(16*KR*W^4)≤Tsecond→
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
    let left:=fun (Dart : Id) (χ ξ : RayCharacter)=>normalizedCosts U c s η
      (fixedPair η C D hC E χ (ξ⁻¹)).left C D Dart Q w (normExponent L Pexp ε)
      Z ε δ (3/4) t V 0 X Kfirst KL Cfirst ξfirst κpad W saving
    let right:=fun (Dart : Id) (χ ξ : RayCharacter)=>normalizedCosts U c s η
      (fixedPair η C D hC E χ (ξ⁻¹)).right D C Dart Q w (normExponent L Pexp ε)
      Z ε δ (3/4) t V 0 X Kfirst KR Cfirst ξfirst κpad W saving
    (1+K₀*H₀/(A₀*B₀))^decay*
      ‖physicalAverage sActual ha seed η t C D hC hD E rows Ds weight W Φ Kfirst K₀ H₀ A₀ B₀‖/
        sourceVolume s≤
      ‖commonHeight sActual η t C D‖*referencePrefactor s η C D E Kfirst (Real.log 4)*
        Ckernel*pushCost Cpush mass KL KR W ε*windowMass (degree U) t^2*
        ∑Dart∈artificialDivisors sActual C D hD.1,‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖*
          ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
            ∑i : Fin 4,∑j : Fin 4,Real.sqrt (left Dart χ ξ i*right Dart χ ξ j) := by
  obtain ⟨U,Cpush,Ckernel,hCpush,hCkernel,hbound⟩ := uniform_integrated_windows
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
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hR hH hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η C D hC hD hCD hη hCcap hDcap
    E hE Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst hξfirst hfirst
    χ₀ msecond hm hml hm2 Tsecond X hT hTcap hX hXcap hXupper hWupper hWinv hTupper
    n hret KL KR hKLcap hKRcap hTL hTR seed hseedC hseedD u huC huD sActual
    Ds rows hDs hrows weight mass hmass hweight hDN hKLrows hKRrows hDartCap
    K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀ left right
  let Rwindow:=K₀*H₀/(A₀*B₀)
  have hRwindow : 0<Rwindow := div_pos (mul_pos hK₀ hH₀) (mul_pos hA₀ hB₀)
  let decayWeight:=(1+Rwindow)^decay
  have hdecay : 0≤decayWeight := pow_nonneg (by linarith) _
  let pref:=referencePrefactor s η C D E Kfirst (Real.log 4)
  have hpref : 0≤pref := referencePrefactor_nonneg s η C D E Kfirst (Real.log 4) hKfirst.le
  let push:=pushCost Cpush mass KL KR W ε
  have hpush : 0≤push := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let budget:=fun (Dart : Id) (χ ξ : RayCharacter)=>
    ∑i : Fin 4,∑j : Fin 4,Real.sqrt (left Dart χ ξ i*right Dart χ ξ j)
  have hbudget (Dart : Id) (χ ξ : RayCharacter) : 0≤budget Dart χ ξ :=
    Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>Real.sqrt_nonneg _))
  have htotal : 0≤∑Dart∈artificialDivisors sActual C D hD.1,
      ‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖*
        ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*budget Dart χ ξ :=
    Finset.sum_nonneg (fun Dart _=>mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg (fun χ _=>Finset.sum_nonneg (fun ξ _=>
        mul_nonneg (norm_nonneg _) (hbudget Dart χ ξ)))))
  by_cases havg : physicalAverage sActual ha seed η t C D hC hD E rows Ds weight W
      Φ Kfirst K₀ H₀ A₀ B₀=0
  · rw [havg,norm_zero,mul_zero,zero_div]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (norm_nonneg _) hpref) hCkernel) hpush) (sq_nonneg _)) htotal
  obtain ⟨Fsel,hFsel,hn⟩ := actual_member sActual ha seed η t C D hC hD E rows Ds weight W
    Φ Kfirst K₀ H₀ A₀ B₀ havg
  let matrix:=fun (Dart : Id) (χ ξ : RayCharacter)=>
    ∑p∈Ds×ˢrows,commonPhase C D hC p*
      weightedPair sActual ha C D seed Dart hC.1 hD.1
        (fixedPair η C D hC E χ (ξ⁻¹)).left
        (fixedPair η C D hC E χ (ξ⁻¹)).right t t weight W p
        (physicalKernel Φ (fun _=>logAnnulus) C D E Kfirst K₀ H₀ A₀ B₀ p.2)
  let scale:=(‖scalar C D hC E Kfirst A₀ B₀‖/sourceVolume s)*decayWeight
  have hscale : 0≤scale := mul_nonneg
    (div_nonneg (norm_nonneg _) (sourceVolume_pos s).le) hdecay
  let A:=pref*Ckernel*push*windowMass (degree U) t^2
  have hA : 0≤A := mul_nonneg (mul_nonneg (mul_nonneg hpref hCkernel) hpush) (sq_nonneg _)
  have hmatrix (Dart : Id) (hDart : Dart∈artificialDivisors sActual C D hD.1)
      (hμ : (UniqueFactorizationMonoid.moebius Dart:ℂ)≠0) (χ ξ : RayCharacter) :
      scale*‖matrix Dart χ ξ‖≤A*budget Dart χ ξ := by
    let P:=fixedPair η C D hC E χ (ξ⁻¹)
    have hsf := squarefree_of_moebius_ne_zero Dart hμ
    have hh := hbound θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical
      hR hH hholes hHR hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η C D hC hD hCD
      hη hCcap hDcap E hE χ (ξ⁻¹) P Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock
      hCfirst hξfirst hfirst χ₀ msecond hm hml hm2 Dart hsf hsf.ne_zero (hDartCap Dart hDart hμ)
      Tsecond X hT hTcap hX hXcap hXupper hWupper hWinv hTupper n hret hKLcap hKRcap hTL hTR
    let rawL:=rawCosts U c s η P.left C D Dart Q w (normExponent L Pexp ε)
      Z ε δ (3/4) t V 0 X Kfirst KL Cfirst ξfirst κpad W saving
    let rawR:=rawCosts U c s η P.right D C Dart Q w (normExponent L Pexp ε)
      Z ε δ (3/4) t V 0 X Kfirst KR Cfirst ξfirst κpad W saving
    have hkernel := (hh.2.2 seed hseedC hseedD u huC huD t t A₀ B₀ hA₀ hB₀).2
      Ds rows hDs hrows weight mass hmass hweight hDN hKLrows hKRrows
    have hk := hkernel.2
      (fun _=>Real.log (((Kfirst/‖eisEmbedding (primeSubsetGenerator
        (fun P : CommonIndex C D=>P.val) E)‖^2)/‖eisEmbedding (activeConductor C D)‖^2)/K₀))
      (fun p=>Real.log (‖eisEmbedding p.2‖^2/H₀)) (commonPhase C D hC)
      (fun p _=>commonPhase_norm C D hC p) Rwindow hRwindow
    change decayWeight*‖matrix Dart χ ξ‖≤
      Ckernel*(push*(∑i : Fin 4,∑j : Fin 4,
        windowBudget (degree U) t (rawL i)*windowBudget (degree U) t (rawR j))) at hk
    have hnormalized := normalize_window_cost sActual ha seed Fsel η t C D hC hD hCD E
      χ (ξ⁻¹) P rows Φ Kfirst K₀ H₀ A₀ B₀ Z hKfirst hA₀ hB₀ hZ hn
      (degree U) rawL rawR hh.1 hh.2.1
    change (‖scalar C D hC E Kfirst A₀ B₀‖/sourceVolume s)*
      (∑i : Fin 4,∑j : Fin 4,windowBudget (degree U) t (rawL i)*windowBudget (degree U) t (rawR j))≤
      pref*windowMass (degree U) t^2*budget Dart χ ξ at hnormalized
    have hs := mul_le_mul_of_nonneg_left hk
      (div_nonneg (norm_nonneg (scalar C D hC E Kfirst A₀ B₀)) (sourceVolume_pos s).le)
    have hn' := mul_le_mul_of_nonneg_left hnormalized (mul_nonneg hCkernel hpush)
    calc
      _≤(Ckernel*push)*((‖scalar C D hC E Kfirst A₀ B₀‖/sourceVolume s)*
          (∑i : Fin 4,∑j : Fin 4,windowBudget (degree U) t (rawL i)*windowBudget (degree U) t (rawR j))) :=
        by convert hs using 1 <;> (try dsimp only [scale]) <;> ring
      _≤(Ckernel*push)*(pref*windowMass (degree U) t^2*budget Dart χ ξ) := hn'
      _=_ := by dsimp only [A]; ring
  have hprojected := projected_norm_bound (artificialDivisors sActual C D hD.1)
    (activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E))
    (QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _)
    (pairCoeff firstPhaseTable) matrix scale A hscale hA budget hbudget hmatrix
  have he := selected_physical_average sActual ha seed η t C D hC hD hCD E rows hrows
    Ds weight W hWblock (fun F hF=>(hweight F hF).1) Φ (fun _=>logAnnulus)
    Kfirst K₀ H₀ A₀ B₀ hKfirst hK₀ hH₀ hA₀ hB₀
  change physicalAverage sActual ha seed η t C D hC hD E rows Ds weight W
      Φ Kfirst K₀ H₀ A₀ B₀=commonHeight sActual η t C D*scalar C D hC E Kfirst A₀ B₀*
    (∑Dart∈artificialDivisors sActual C D hD.1,(UniqueFactorizationMonoid.moebius Dart:ℂ)*
      activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)*
      ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*matrix Dart χ ξ) at he
  rw [he,norm_mul,norm_mul]
  have hs := mul_le_mul_of_nonneg_left hprojected (norm_nonneg (commonHeight sActual η t C D))
  convert hs using 1 <;> (try dsimp only [scale,decayWeight,Rwindow,A,pref,push,budget]) <;> ring

end
end Candidate.Feedback.FourthPower.MixedFirstPhysicalBudget
