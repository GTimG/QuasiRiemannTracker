/- Copyright (c) 2026 Sil. Apache-2.0.
The actual first positive energy, with all four numerical suppliers and
the exact two-side reference normalization.
-/
import Candidate.Feedback.FourthPower.MixedFirstExceptionalApplication
import Candidate.Feedback.FourthPower.MixedFirstReferencePair
import Candidate.Feedback.FourthPower.MixedFirstInactiveConductor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedFirstFullBudget
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open ActualEisensteinCubic CenteredMomentRankinRadical
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstMixedAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstWindowBudgets
open CenteredMomentFirstDiscardedEnergy CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSmoothedWindowEnergy
open CenteredMomentGaussEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalNormCap MixedOriginalTail
open MixedOriginalSecondZero MixedFirstLiveSource
open MixedInnerExceptionalBlock
open MixedFirstFourParts MixedFirstActualNonexceptional MixedFirstAllocatedRemainders
open MixedFirstNonexceptionalAllocation MixedFirstReferencePair MixedFirstInactiveConductor
open MixedFirstExceptionalNormalization MixedFirstExceptionalApplication
open MixedHeightEnvelope ReferencePrimeEnclosure MixedCompletedRows
open QuadraticInitialBound
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- These finite controls are selected before the fixed original
character, profiles, heights and every common/allocation label. -/
structure Controls where
  nonexceptionalDegree : ℕ
  nonexceptionalControl : Finset (ℕ×ℕ)
  exceptionalDegree : ℕ
  exceptionalControl : Finset (ℕ×ℕ)
  tailControl : Finset (ℕ×ℕ)

/-- Numerical constants only. No source or energy estimate is a field. -/
structure Constants where
  source : ℝ
  physical : ℝ
  geometry : ℝ
  nonexceptionalCount : ℝ
  zero : ℝ
  tail : ℝ
  kernel : ℝ
  exceptional : ℝ
  exceptionalSum : ℝ
  exceptionalCount : ℝ
  source_pos : 0<source
  physical_pos : 0<physical
  geometry_pos : 0<geometry
  nonexceptionalCount_pos : 0<nonexceptionalCount
  zero_pos : 0<zero
  tail_pos : 0<tail
  kernel_nonneg : 0≤kernel
  exceptional_pos : 0<exceptional
  exceptionalSum_pos : 0<exceptionalSum
  exceptionalCount_pos : 0<exceptionalCount

def canonicalProfile (U : Controls) (c : Constants) (s : Source ι a b)
    (t V : ℝ) : ℝ :=
  c.source*diagonalControl ballProfile*
    (sourceControl U.nonexceptionalControl s.W₁*sourceControl U.nonexceptionalControl s.W₂)^2*
    sourceHeight t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))^U.nonexceptionalDegree

def zeroCost (c : Constants) (s : Source ι a b) (G Dart : Id)
    (Z ε δ X Kchild W : ℝ) : ℝ :=
  (16*Kchild*W^3)*‖paperRadialFourier ballProfile 0‖*
    (c.zero*(G.absNorm:ℝ)^δ*(∏i,s.M i)^2*(profileCap s)^2*X^(1+ε)/
      ((G.absNorm:ℝ)*(Dart.absNorm:ℝ)))

def nonexceptionalCost (U : Controls) (c : Constants) (s : Source ι a b)
    (G Dart : Id) (τ : Character) (w : ι→ℝ)
    (Z ε δ κ t V tp W : ℝ) : ℝ :=
  c.nonexceptionalCount*(G.absNorm:ℝ)^δ*
    fullCost s.P s.M U.nonexceptionalDegree c.physical c.geometry Z
      (κ*(∑i,w i)+2*ε+δ) (canonicalProfile U c s t V) b s.T tp W Dart s.d*
      (τ.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2

def tailCost (U : Controls) (c : Constants) (s : Source ι a b)
    (G Dart : Id) (Z δ saving : ℝ) : ℝ :=
  c.tail*(G.absNorm:ℝ)^δ*(∏i,s.M i)^2*(profileCap s)^2*
    U.tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)/
      ((G.absNorm:ℝ)*(Dart.absNorm:ℝ))

/-- Four numerical costs, in exactly the order of FourParts.components.
The exceptional supplier is already normalized by reference, so only
that entry is multiplied back by its one actual reference factor. -/
def rawCosts (U : Controls) (c : Constants) (s : Source ι a b)
    (η τ : Character) (G Gopp Dart Q : Id) (w : ι→ℝ)
    (Bnorm Z ε δ κsource t V tp X Kfirst Kchild Cfirst ξfirst κpad W saving : ℝ) : Fin 4→ℝ :=
  ![zeroCost c s G Dart Z ε δ X Kchild W,
    nonexceptionalCost U c s G Dart τ w Z ε δ κsource t V tp W,
    reference τ G Gopp (sourceVolume s) Z*
      numericalCost s η G Dart Q U.exceptionalDegree U.exceptionalControl
        Bnorm ε δ ε δ c.kernel c.exceptional c.exceptionalSum c.exceptionalCount
        Z Kfirst Cfirst ξfirst κpad W tp,
    tailCost U c s G Dart Z δ saving]

def normalizedCosts (U : Controls) (c : Constants) (s : Source ι a b)
    (η τ : Character) (G Gopp Dart Q : Id) (w : ι→ℝ)
    (Bnorm Z ε δ κsource t V tp X Kfirst Kchild Cfirst ξfirst κpad W saving : ℝ) : Fin 4→ℝ :=
  fun i=>rawCosts U c s η τ G Gopp Dart Q w Bnorm Z ε δ κsource t V tp X
    Kfirst Kchild Cfirst ξfirst κpad W saving i/reference τ G Gopp (sourceVolume s) Z

theorem reference_pos (s : Source ι a b) (τ : Character) (G Gopp : Id)
    (hG : G≠0) (Z : ℝ) (hZ : 0<Z) : 0<reference τ G Gopp (sourceVolume s) Z := by
  have hv := sourceVolume_pos s
  have hτ : 0<(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hg : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  unfold reference
  positivity

/-- Elementary sum expansion; the two index sets are independent, so
zero/exceptional and tail/nonexceptional cross terms are included. -/
private theorem sqrt_pair_sum (A B : Fin 4→ℝ) (hA : ∀i,0≤A i) (hB : ∀j,0≤B j) :
    Real.sqrt ((∑i,A i)*(∑j,B j))≤∑i,∑j,Real.sqrt (A i*B j) := by
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _=>hA i))]
  have hleft := CenteredMomentFirstWindowBudgets.sqrt_sum_le Finset.univ A (fun i _=>hA i)
  have hright := CenteredMomentFirstWindowBudgets.sqrt_sum_le Finset.univ B (fun j _=>hB j)
  apply (mul_le_mul hleft hright (Real.sqrt_nonneg _) (by positivity)).trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (Real.sqrt_mul (hA i) (B j)).symm

/-- Structural two-side normalization at INDEPENDENT child scales.
The four numerical bounds in this private helper are discharged below
by the four actual suppliers, not exported as analytic premises. -/
private theorem actual_reference_from_costs (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (seed Dart : Id)
    (η : Character) (m A : O) (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (χ ξ : RayCharacter) (F : FixedPair η C D hC E χ ξ)
    (hseedC : seed∣C) (hseedD : seed∣D)
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (windows : Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z tleft tright KL KR W Tsec ξsec : ℝ)
    (hK : 0<K) (hA : 0<A₀) (hB : 0<B₀) (hZ : 1<Z)
    (hKL : 0<KL) (hKR : 0<KR) (hW : 0<W)
    (hwin : ∀i y,windows i y≠0→|y|≤M)
    (hn : block η m A t (sourceColumns s) (sourceCoefficient s ha seed)
      C D hC hD E rows Φ windows K K₀ H₀ A₀ B₀≠0)
    (Q : Id) (msecond : O) (χ₀ : RayCharacter) (left right : Fin 4→ℝ)
    (hleft : ∀i,components s ha hb cover C Dart F.left tleft KL W Tsec Z ξsec Q msecond χ₀ i≤left i)
    (hright : ∀i,components s ha hb cover D Dart F.right tright KR W Tsec Z ξsec Q msecond χ₀ i≤right i) :
    ‖scalar C D hC E K A₀ B₀‖/sourceVolume s*
      Real.sqrt (actualEnergy s ha D C hC seed Dart F.left tleft KL W*
        actualEnergy s ha C D hD seed Dart F.right tright KR W)≤
    ‖inactiveWeight C D E‖*(Real.exp M/(a^2/pairNorm s.d))*fixedPresentationCost*K*
      (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*
        ∑i : Fin 4,∑j : Fin 4,
          Real.sqrt ((left i/reference F.left C D (sourceVolume s) Z)*
            (right j/reference F.right D C (sourceVolume s) Z)) := by
  have hl0 (i : Fin 4) : 0≤left i :=
    (components_nonneg s ha hb cover C Dart F.left tleft KL W Tsec Z ξsec Q msecond χ₀ i).trans (hleft i)
  have hr0 (i : Fin 4) : 0≤right i :=
    (components_nonneg s ha hb cover D Dart F.right tright KR W Tsec Z ξsec Q msecond χ₀ i).trans (hright i)
  have hl := (actual_energy_four_parts s ha hb cover D C seed Dart hD hC hCD.symm hseedC
    F.left tleft KL W Tsec Z ξsec hKL hW Q msecond χ₀).trans
      (Finset.sum_le_sum (fun i _=>hleft i))
  have hr := (actual_energy_four_parts s ha hb cover C D seed Dart hC hD hCD hseedD
    F.right tright KR W Tsec Z ξsec hKR hW Q msecond χ₀).trans
      (Finset.sum_le_sum (fun i _=>hright i))
  have henergy (G Gopp : Id) (hG : Supported G) (τ : Character) (v Kc : ℝ) (hKc : 0<Kc) :
      0≤actualEnergy s ha Gopp G hG seed Dart τ v Kc W := by
    dsimp only [actualEnergy]
    apply div_nonneg _ hW.le
    have hs := gaussEnergy_hasSum_re Finset.univ
      (CenteredMomentFirstPhysicalSource.element Gopp G hG.1 (sourceColumns s))
      (CenteredMomentFirstPhysicalSource.element_supported Gopp G hG.1 (sourceColumns s))
      (fun I : CenteredMomentFirstPhysicalSource.columns Gopp G hG.1 (sourceColumns s)=>
        originalResidual s ha seed G Dart I*heightCoeff τ v I)
      ballProfile (16*Kc*W^4) (by positivity)
    rw [←hs.tsum_eq]
    exact tsum_nonneg (fun z=>mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))
  have hrefL := reference_pos s F.left C D hC.1 Z (zero_lt_one.trans hZ)
  have hrefR := reference_pos s F.right D C hD.1 Z (zero_lt_one.trans hZ)
  let EL := ∑i,left i/reference F.left C D (sourceVolume s) Z
  let ER := ∑i,right i/reference F.right D C (sourceVolume s) Z
  have hEL : 0≤EL := Finset.sum_nonneg (fun i _=>div_nonneg (hl0 i) hrefL.le)
  have hER : 0≤ER := Finset.sum_nonneg (fun i _=>div_nonneg (hr0 i) hrefR.le)
  have hsumL : (∑i,left i)=reference F.left C D (sourceVolume s) Z*EL := by
    dsimp only [EL]
    rw [←Finset.sum_div]
    field_simp [hrefL.ne']
  have hsumR : (∑i,right i)=reference F.right D C (sourceVolume s) Z*ER := by
    dsimp only [ER]
    rw [←Finset.sum_div]
    field_simp [hrefR.ne']
  have hroot := Real.sqrt_le_sqrt (mul_le_mul hl hr
    (henergy D C hD F.right tright KR hKR) (Finset.sum_nonneg (fun i _=>hl0 i)))
  rw [hsumL,hsumR] at hroot
  have hphysical := actual_source_reference_pair s ha seed η m A t C D hC hD hCD E χ ξ F
    rows Φ windows K K₀ H₀ A₀ B₀ M Z EL ER hK hA hB hZ hEL hER hwin hn
  have hpref : 0≤‖inactiveWeight C D E‖*(Real.exp M/(a^2/pairNorm s.d))*fixedPresentationCost*K*
      (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm := by
    have := fixedPresentationCost_pos.le
    have := (pairNorm_pos s.hd.1 s.hd.2).le
    positivity
  calc
    _≤‖scalar C D hC E K A₀ B₀‖/sourceVolume s*
        Real.sqrt ((reference F.left C D (sourceVolume s) Z*EL)*
          (reference F.right D C (sourceVolume s) Z*ER)) :=
      mul_le_mul_of_nonneg_left hroot (div_nonneg (norm_nonneg _) (sourceVolume_pos s).le)
    _≤_ := hphysical.trans (mul_le_mul_of_nonneg_left
      (sqrt_pair_sum _ _ (fun i=>div_nonneg (hl0 i) hrefL.le)
        (fun i=>div_nonneg (hr0 i) hrefR.le)) hpref)

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- All four ACTUAL suppliers, followed by the genuine two-side
reference normalization. There is no energy or source-bound premise.
The remaining inequalities concern only original source geometry and
the chosen physical cutoffs. KL and KR are never identified.

This is the full first positive-source budget, not the final mixed
moment: annular Fourier assembly and its outer finite sums remain. -/
theorem uniform_full_budget
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BG BH Bsource Bη Pexp Mgeom Btail
      ε δ lo hi κsource ξsecond saving : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hMcap0 : 0<Mcap)
    (hL : 0≤L) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBG : 0≤BG) (hBH : 0≤BH) (hBsource : 0≤Bsource)
    (hPexp : 0≤Pexp) (hMgeom : 0≤Mgeom) (hBtail : 0≤Btail) (hBGtail : BG≤Btail)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hgap : (7/10:ℝ)+2*δ<1) (hξsecond : 0<ξsecond)
    (hMcap : Mgeom+(Bη+BG+ε)+Bsource+ε≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ : 2*HeckeZeroSupremum.beta-1≤κsource)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃U : Controls,∀η₀ : Character,Q≤η₀.modulus→∃c : Constants,
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
      CompletedGauss.primeSupport C=CompletedGauss.primeSupport D→
      (η.modulus.absNorm:ℝ)≤Z^Bη→(C.absNorm:ℝ)≤Z^BG→(D.absNorm:ℝ)≤Z^BG→
    ∀(E : Finset (CommonIndex C D)),E∈inactiveSubsets C D→
    ∀(χ ξ : RayCharacter)(F : FixedPair η C D hC E χ ξ),
    ∀(Kfirst Tfirst Cfirst ξfirst κpad W : ℝ),0<Kfirst→0<W→1≤Cfirst→0≤ξfirst→
      Tfirst≤Cfirst*firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) Kfirst (sourceVolume s)→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀Dart : Id,Squarefree Dart→Dart≠0→(Dart.absNorm:ℝ)≤Z^Btail→
    ∀(tleft tright Tsecond X : ℝ),0≤Tsecond→Tsecond≤Z^(Mgeom-ξsecond)→
      1≤X→(2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d≤X→
      X≤Z^Btail→W≤Z^Btail→W⁻¹≤Z^Btail→Tsecond≤Z^Btail→
    ∀n : ℤ,Retained (frequencyRadius Tfirst Z ξfirst) n→
    let KL:=nominalChildScale C D E Kfirst (sourceVolume s) Z κpad n
    let KR:=nominalChildScale D C (swapSubset C D E) Kfirst (sourceVolume s) Z κpad n
    KL≤Z^Btail→KR≤Z^Btail→X^2/(16*KL*W^4)≤Tsecond→X^2/(16*KR*W^4)≤Tsecond→
    let left:=rawCosts U c s η F.left C D Dart Q w (normExponent L Pexp ε)
      Z ε δ κsource t V tleft X Kfirst KL Cfirst ξfirst κpad W saving
    let right:=rawCosts U c s η F.right D C Dart Q w (normExponent L Pexp ε)
      Z ε δ κsource t V tright X Kfirst KR Cfirst ξfirst κpad W saving
    (∀i,components s ha (zero_le_one.trans hb) cover C Dart F.left tleft KL W Tsecond Z ξsecond Q msecond χ₀ i≤left i) ∧
    (∀i,components s ha (zero_le_one.trans hb) cover D Dart F.right tright KR W Tsecond Z ξsecond Q msecond χ₀ i≤right i) ∧
    ∀seed : Id,seed∣C→seed∣D→∀(m A : O)(tphys : ℝ)(rows : Finset O)(Φ : 𝓢(ℝ,ℂ))
      (windows : Fin 4→ℝ→ℂ)(K₀ H₀ A₀ B₀ Mwindow : ℝ),0<A₀→0<B₀→
      (∀i y,windows i y≠0→|y|≤Mwindow)→
      block η m A tphys (sourceColumns s) (sourceCoefficient s ha seed)
        C D hC hD E rows Φ windows Kfirst K₀ H₀ A₀ B₀≠0→
    ‖scalar C D hC E Kfirst A₀ B₀‖/sourceVolume s*
      Real.sqrt (actualEnergy s ha D C hC seed Dart F.left tleft KL W*
        actualEnergy s ha C D hD seed Dart F.right tright KR W)≤
    ‖inactiveWeight C D E‖*(Real.exp Mwindow/(a^2/pairNorm s.d))*fixedPresentationCost*Kfirst*
      (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*
        ∑i : Fin 4,∑j : Fin 4,
          Real.sqrt ((left i/reference F.left C D (sourceVolume s) Z)*
            (right j/reference F.right D C (sourceVolume s) Z)) := by
  obtain ⟨Jn,cn,hn⟩ := uniform_actual_allocated_part (ι:=ι) M Hray hHray N Holes hcard Wslot
    a b Mcap L Lslot Lcap Cap BR BG BH Bsource (Bη+BG+ε) ε δ δ lo hi κsource Mgeom 1 ε ε
    hWs hW ha haUpper hb hMcap0 hLslot hLcap hCap hBR hBG hBH hBsource hCapb hLordinary
    hε hδ hδ hMgeom zero_lt_one hε hε hMcap hβ hκ Q hQt hQ72 hQM
  obtain ⟨Czero,hCzero,hzero⟩ := uniform_allocated_zero N ε δ hε hδ
  obtain ⟨ct,Ctail,hCtail,htail⟩ := uniform_allocated_discarded N Btail ξsecond saving δ hBtail hξsecond hδ
  obtain ⟨Je,ce,hce,Ckernel,hCkernel,he⟩ := uniform_fixed_pair_components N
    (7/10) a b ε δ ε δ ε L Pexp Bη BR BG BH Mgeom
    (by norm_num) (by norm_num) ha (zero_le_one.trans hb) hε hδ hgap hε hδ hε hL hPexp hBH hMgeom
  obtain ⟨Ae,Csum,CcountE,hAe,hCsum,hCcountE,he⟩ := he Q (NeZero.ne Q) hQt hQ72
  let U : Controls:=⟨Jn,cn,Je,ce,ct⟩
  refine ⟨U,?_⟩
  intro η₀ hη₀
  obtain ⟨Cs,Cp,Cg,CcountN,hCs,hCp,hCg,hCcountN,hn⟩ := hn η₀ hη₀
  let c : Constants:=⟨Cs,Cp,Cg,CcountN,Czero,Ctail,Ckernel,Ae,Csum,CcountE,
    hCs,hCp,hCg,hCcountN,hCzero,hCtail,hCkernel,hAe,hCsum,hCcountE⟩
  have hfixed : ∀ᶠZ : ℝ in atTop,fixedPresentationCost≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) fixedPresentationCost
  refine ⟨c,?_⟩
  filter_upwards [hn,htail,he,hfixed] with Z hn htail he hfixed
  obtain ⟨hZ,hn⟩ := hn
  refine ⟨hZ,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hR hH hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η C D hC hD hCD hη hCcap hDcap
    E hE χ ξ F Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst hξfirst hfirst
    χ₀ msecond hm hml hm2 Dart hDart hDart0 hDartCap tleft tright Tsecond X hT hTcap
    hX hXcap hXupper hWupper hWinv hTupper n hret KL KR hKLcap hKRcap hTL hTR left right
  have hz := zero_lt_one.trans hZ
  have hKL : 0<KL := Real.rpow_pos_of_pos hz _
  have hKR : 0<KR := Real.rpow_pos_of_pos hz _
  have hXpos : 0<X := zero_lt_one.trans_le hX
  have hCtail : (C.absNorm:ℝ)≤Z^Btail := hCcap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hBGtail)
  have hDtail : (D.absNorm:ℝ)≤Z^Btail := hDcap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hBGtail)
  have hmod : (F.left.modulus.absNorm:ℝ)≤Z^(Bη+BG+ε) ∧
      (F.right.modulus.absNorm:ℝ)≤Z^(Bη+BG+ε) := by
    have hc := fixed_pair_common_caps η C D hC hD.1 E hE χ ξ F
    have hbound : fixedPresentationCost*(η.modulus.absNorm:ℝ)*min (C.absNorm:ℝ) (D.absNorm:ℝ)
        ≤Z^(Bη+BG+ε) := by
      calc
        _≤Z^ε*Z^Bη*Z^BG :=
          mul_le_mul (mul_le_mul hfixed hη (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _))
            ((min_le_left _ _).trans hCcap)
            (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)
        _=_ := by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
    exact ⟨hc.1.trans hbound,hc.2.trans hbound⟩
  have hTcapHalf : Tsecond≤Z^(Mgeom-ξsecond/2) := hTcap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hradius : frequencyRadius Tsecond Z ξsecond≤Z^Mgeom := by
    unfold frequencyRadius
    calc
      _≤Z^(Mgeom-ξsecond/2)*Z^(ξsecond/2) :=
        mul_le_mul_of_nonneg_right hTcapHalf (Real.rpow_nonneg hz.le _)
      _=_ := by rw [←Real.rpow_add hz];congr 1;ring
  have hnonex := hn θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
    s hcanonical hR hH hholes hHR hX₁ hX₂ hY₁ hY₂ hsource cover
  have hnl := hnonex C Dart hC.1 hCcap hDart F.left tleft KL W Tsecond ξsecond msecond χ₀
    hmod.1 hKL hWblock hm hml hm2 (by simpa only [one_mul] using hradius)
  have hnr := hnonex D Dart hD.1 hDcap hDart F.right tright KR W Tsecond ξsecond msecond χ₀
    hmod.2 hKR hWblock hm hml hm2 (by simpa only [one_mul] using hradius)
  have hzL := hzero ι a b s hcard ha (zero_le_one.trans hb) cover C Dart hC.1 hDart0
    F.left tleft X KL W hX hXcap hKL.le hWblock.le
  have hzR := hzero ι a b s hcard ha (zero_le_one.trans hb) cover D Dart hD.1 hDart0
    F.right tright X KR W hX hXcap hKR.le hWblock.le
  have htL := htail.2 ι a b s hcard ha (zero_le_one.trans hb) cover C Dart hC.1 hDart0
    hCtail hDartCap F.left tleft KL W X Tsecond hKL hWblock hXpos hpool hXcap hXupper
    hKLcap hWupper hWinv hTupper hTL
  have htR := htail.2 ι a b s hcard ha (zero_le_one.trans hb) cover D Dart hD.1 hDart0
    hDtail hDartCap F.right tright KR W X Tsecond hKR hWblock hXpos hpool hXcap hXupper
    hKRcap hWupper hWinv hTupper hTR
  have hex := he.2 ι s cover hcard hX₁ hX₂ hY₁ hY₂ hP hR hF η C D hC hD hCD
    hη hCcap hDcap E χ ξ F Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst
    hξfirst hfirst χ₀ msecond hm hml hm2 Dart hDart hDart0 tleft tright Tsecond ξsecond
    hT hTcapHalf n hret
  have hrefL := reference_pos s F.left C D hC.1 Z hz
  have hrefR := reference_pos s F.right D C hD.1 Z hz
  have heL := (div_le_iff₀ hrefL).mp hex.1
  have heR := (div_le_iff₀ hrefR).mp hex.2
  have hexponent : κsource*(∑i,w i)+ε+δ+ε=κsource*(∑i,w i)+2*ε+δ := by ring
  have hl : ∀i,components s ha (zero_le_one.trans hb) cover C Dart F.left tleft
      KL W Tsecond Z ξsecond Q msecond χ₀ i≤left i := by
    intro i
    fin_cases i
    · exact hzL
    · change allocatedPart s ha (zero_le_one.trans hb) cover C Dart F.left tleft
        KL W Tsecond Z ξsecond Q msecond χ₀ ≤
        nonexceptionalCost U c s C Dart F.left w Z ε δ κsource t V tleft W
      simpa only [nonexceptionalCost,canonicalProfile,U,c,
        Controls.nonexceptionalDegree,Controls.nonexceptionalControl,Constants.source,
        Constants.physical,Constants.geometry,Constants.nonexceptionalCount,hexponent] using hnl
    · change components s ha (zero_le_one.trans hb) cover C Dart F.left tleft
        KL W Tsecond Z ξsecond Q msecond χ₀ 2 ≤
        reference F.left C D (sourceVolume s) Z *
          numericalCost s η C Dart Q Je ce (normExponent L Pexp ε)
            ε δ ε δ Ckernel Ae Csum CcountE Z Kfirst Cfirst ξfirst κpad W tleft
      simpa only [KL,Controls.exceptionalDegree,Controls.exceptionalControl,
        Constants.kernel,Constants.exceptional,Constants.exceptionalSum,Constants.exceptionalCount,
        mul_comm] using heL
    · exact htL
  have hr : ∀i,components s ha (zero_le_one.trans hb) cover D Dart F.right tright
      KR W Tsecond Z ξsecond Q msecond χ₀ i≤right i := by
    intro i
    fin_cases i
    · exact hzR
    · change allocatedPart s ha (zero_le_one.trans hb) cover D Dart F.right tright
        KR W Tsecond Z ξsecond Q msecond χ₀ ≤
        nonexceptionalCost U c s D Dart F.right w Z ε δ κsource t V tright W
      simpa only [nonexceptionalCost,canonicalProfile,U,c,
        Controls.nonexceptionalDegree,Controls.nonexceptionalControl,Constants.source,
        Constants.physical,Constants.geometry,Constants.nonexceptionalCount,hexponent] using hnr
    · change components s ha (zero_le_one.trans hb) cover D Dart F.right tright
        KR W Tsecond Z ξsecond Q msecond χ₀ 2 ≤
        reference F.right D C (sourceVolume s) Z *
          numericalCost s η D Dart Q Je ce (normExponent L Pexp ε)
            ε δ ε δ Ckernel Ae Csum CcountE Z Kfirst Cfirst ξfirst κpad W tright
      simpa only [KR,Controls.exceptionalDegree,Controls.exceptionalControl,
        Constants.kernel,Constants.exceptional,Constants.exceptionalSum,Constants.exceptionalCount,
        mul_comm] using heR
    · exact htR
  refine ⟨hl,hr,?_⟩
  intro seed hseedC hseedD m A tphys rows Φ windows K₀ H₀ A₀ B₀ Mwindow hA hB hwin hblock
  exact actual_reference_from_costs s ha (zero_le_one.trans hb) cover seed Dart η m A tphys
    C D hC hD hCD E χ ξ F hseedC hseedD rows Φ windows
    Kfirst K₀ H₀ A₀ B₀ Mwindow Z tleft tright KL KR W Tsecond ξsecond
    hKfirst hA hB hZ hKL hKR hWblock hwin hblock Q msecond χ₀ left right hl hr

end
end Candidate.Feedback.FourthPower.MixedFirstFullBudget
