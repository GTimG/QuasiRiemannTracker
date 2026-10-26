/- Copyright (c) 2026 Sil. Apache-2.0.
The actual avoided native retained remainder, with ORIGINAL harmonic
seed payment. The raw volume is squared, as required by the supplier.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallRetained
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedActualNonexceptionalBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallClosed
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstSectors
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentUncenteredTerminal HeckeDyadic
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedNativeFloor MixedInnerExceptionalBlock MixedFirstActualNonexceptional
open MixedFirstProfileEnvelope MixedCanonicalSource MixedFirstAvoidance OuterFreshSelectedWindow
open RepairedSmallRowAllocation RepairedSmallRawBudget RepairedSmallNativeRaw RepairedSmallNativeFamily
open QuadraticInitialBound
open CenteredMomentCanonicalFirst
open CenteredMomentSecondNonexceptionalScalar
open MixedPoissonLocalization
open MixedOriginalTail
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι]
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)


open RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondEnergySplit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily
open MixedActualFamily MixedPhysicalEnvelopes MixedRawEnvelope
open RepairedSmallAvoidedNative


open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentCompleteCommon
open MixedCanonicalEnvelope MixedOriginalCoprimality MixedOriginalNormCap
open MixedInnerExceptionalLedger MixedActualGeometry
open RepairedSmallPhysical


open CenteredMomentSecondLiveBlock CenteredMomentSecondActivePhysicalDictionary
open MixedActualRetained MixedLocalizedDictionary RepairedSmallActivePhysical


open MixedActualNonexceptionalBound RepairedSmallRetained

theorem uniform_avoided_nonexceptional
    (Holes : ℕ) (Wslot : ℝ → ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi Lradius Cr εg : ℝ)
    (hWs : Function.support Wslot⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hMcap : 0≤Mcap) (hε : 0<ε) (hδCount : 0<δCount) (hδPhys : 0<δPhys)
    (hLradius : 0≤Lradius) (hCr : 0<Cr) (hεg : 0<εg)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M)

 :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp Cg : ℝ,0<Cs ∧ 0<Cp ∧ 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι → RayQuotient.Characters M Hray)(w σ freq : ι → ℝ)(t₀ V : ℝ)
      (R₀ : ι → Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) → (∑i,w i)≤rho →
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s →
      (∀i,1≤s.M i) → (s.R.absNorm:ℝ)≤Z^BR →
      s.H⊆ReferencePrimeEnclosure.enclosure (Cap*Z^Lcap) →
      ((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH →
      (∀i,∀P∈s.H,P.val∈R₀ i) →
      s.X₁≤Z^L → s.X₂≤Z^L → s.Y₁≤Z^L → s.Y₂≤Z^L →
      sourceNormCap s.P b s.T s.d≤Z^Bnorm →
    ∀cover : OriginalEnclosure s,∀u seed : Id,Squarefree seed → u∣s.R*seed →
    let Sco:=sourceColumns s;
    let beta:=sourceCoefficient (avoidSource s u) ha seed;
    let A:=Cs*slotCost s*diagonalControl ballProfile*
      (sourceControl control s.W₁*sourceControl control s.W₂)^2*
      (height t₀ V s.t₁ s.t₂)^degree;
    let base:=(3/4:ℝ)*rho+ε+Bnorm*δCount;

    let Hsource:=sourceNormCap s.P b s.T s.d;
    ∀(η : Character)(tp K Wblock Tsec ξ : ℝ)(m : O)(χ₀ : RayCharacter),
      0<K → 0<Wblock → m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      frequencyRadius Tsec Z ξ≤Cr*Z^Lradius →
    ∀Rdecl : (p : ActiveLabel Sco beta) → (U : Finset (CommonIndex p.val.1 p.val.2)) →
      SourceBlocks p.val.1 p.val.2 U (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource → ℝ,
    (∀p∈liveLabels η Sco beta,∀U,
      ∀n : SourceBlocks p.val.1 p.val.2 U (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource,
      physicalBlock η tp Sco beta p.val.1 p.val.2
        (commonLabels_supported (activeSource Sco beta) _ _ p.property).1
        (commonLabels_supported (activeSource Sco beta) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i => (n i:ℤ))≠0 →
      Real.logb Z (frequencyRadius Tsec Z ξ)+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤Rdecl p U n ∧
        Rdecl p U n≤Mcap) →
      ‖localizedDensity Finset.univ (sourceGenerator Sco) (sourceGenerator_supported Sco)
          (fun I : supportedColumns Sco => beta I*heightCoeff η tp I) K Wblock
          (retainedWeight (frequencyRadius Tsec Z ξ))-
        partEnergy true η χ₀ Q m tp Sco beta ballProfile (16*K*Wblock^4)
          Tsec Z ξ Hsource/(Wblock:ℂ)‖≤
      closedBudget (Fintype.card ι) degree Cp Cg Z (base+δPhys+εg)
        A b (sourceVolume s) tp Wblock η seed s.d
 := by
  obtain ⟨degree,control,hretained⟩ := uniform_avoided_retained (ι:=ι) M Hray hHray
    Holes Wslot a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi
    hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary hBR hBH hBnorm hMcap
    hε hδCount hδPhys hβ Q hQt hQ72 hQM
  obtain ⟨Cg,hCg,hgeometry⟩ := uniform_fourth_retained_geometry Bnorm Lradius Cr εg
    hBnorm hLradius hCr hεg
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  obtain ⟨Cs,Cp,hCs,hCp,hretained⟩ := hretained η₀ hQη₀
  refine ⟨Cs,Cp,Cg,hCs,hCp,hCg,?_⟩
  filter_upwards [hretained,hgeometry] with Z hZ hgZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap cover u seed hseed hu
    Sco beta A base Hsource η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 hradius Rdecl hadmissible
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hvolume := sourceVolume_pos s
  have hA : 0≤A := by
    have hs := slot_cost_nonneg s
    have hd := diagonalControl_nonneg ballProfile
    have hh : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    dsimp only [A]
    positivity
  have hHsource : 0≤Hsource := by
    have ht := s.total_pos
    have hp := pairNorm_pos s.hd.1 s.hd.2
    have hP (i : ι) : 0<s.P i := zero_lt_one.trans_le (s.hP i)
    dsimp only [Hsource,sourceNormCap]
    exact mul_nonneg (mul_nonneg (sq_nonneg b) (div_nonneg ht.le hp.le))
      (Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (hP i).le))
  have hcolumns (I : Id) (hi : beta I≠0) : (I.absNorm:ℝ)≤Hsource :=
    (original_coefficient_cap (avoidSource s u) ha seed I hi).2
  have hseedcol (I : Id) (hI : I∈Sco) (hi : beta I≠0) : seed∣I :=
    source_coefficient_seed (avoidSource s u) ha seed I hi
  have hr := hZ.2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap cover u seed hseed hu
    η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 Rdecl hadmissible
  have hg := hgZ seed hseed hseed.ne_zero η tp Sco beta ballProfile hseedcol
    K Wblock (frequencyRadius Tsec Z ξ) Hsource hK hWblock hHsource hradius
    hsourcecap hcolumns Q m χ₀
  let F:=analyticBudget degree Cp Z δPhys (sourceVolume s) A base tp s.d
  have hF : 0≤F := by
    have hp := (pairNorm_pos s.hd.1 s.hd.2).le
    have hh := (heightEnvelope_pos tp).le
    dsimp only [F,analyticBudget]
    positivity
  apply hr.trans
  calc
    _=F*(fullRetainedGeometry η tp Sco beta ballProfile (16*K*Wblock^4)
      (frequencyRadius Tsec Z ξ) Hsource Q m χ₀/Wblock) := by ring
    _≤F*((4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*η.modulus.absNorm*Hsource)*
      (Cg*Z^εg/(seed.absNorm:ℝ))/Wblock) := mul_le_mul_of_nonneg_left hg hF
    _=_ := by
      have hHs : Hsource=b^2*(2:ℝ)^Fintype.card ι*sourceVolume s/pairNorm s.d := by
        simpa only [Hsource,sourceVolume,s.hpX] using sourceNormCap_eq_volume s.P b s.T s.d
      rw [hHs]
      dsimp only [F,analyticBudget,closedBudget]
      simp only [Real.rpow_add hz]
      have hnseed : (seed.absNorm:ℝ)≠0 := by
        exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero
      field_simp [(pairNorm_pos s.hd.1 s.hd.2).ne',hWblock.ne',hnseed]
      <;> ring

end
end Candidate.FourthPower.RepairedSmallClosed
