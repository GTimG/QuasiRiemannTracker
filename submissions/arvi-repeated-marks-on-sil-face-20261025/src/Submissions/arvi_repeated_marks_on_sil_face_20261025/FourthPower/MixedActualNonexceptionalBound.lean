/- Copyright (c) 2026 Sil. Apache-2.0.
exact retained nonexceptional aggregation for originalColumn.
The actual child-envelope geometry is summed over all actual blocks.
Source estimates are supplied by MixedActualEnvelopePhysical, not assumed.
The localized scale 16*K*Wblock^4 and outer 1/Wblock are unchanged.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedActualRetained

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedActualNonexceptionalBound
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open RayFourExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows MixedCanonicalSource MixedHeightEnergy
open MixedHeightEnvelope MixedRawEnvelope MixedActualEnvelopePhysical MixedLocalizedDictionary
open MixedActualGeometry MixedActualRetained MixedOriginalCoprimality
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondRadicalBudget
open MixedOriginalNormCap MixedLiteralAllocation NativeInjectiveEnergy MixedPoissonLocalization
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentSecondWindowBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondWholeKernel
open CenteredMomentSecondActivePhysicalDictionary
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Fully explicit normalized physical-side cost. A is the displayed
original profile/height factor, while volume is the original raw volume.
No genuine common divisor remains hidden in this expression. -/
def closedBudget (slots degree : ℕ) (Cp Cg Z exponent A b volume tp Wblock : ℝ)
    (η : Character) (seed : Id) (d : Id×Id) : ℝ :=
  4*(fixedFactor:ℝ)*Cp*Cg*A*b^2*(2:ℝ)^slots*(η.modulus.absNorm:ℝ)*volume^2*
    Z^exponent*heightEnvelope tp^(2*degree)*profileMoment degree^2 /
      (pairNorm d^2*(seed.absNorm:ℝ)*Wblock)

variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Concrete retained nonexceptional estimate after both actual source
estimates and the genuine harmonic divisor sum have been supplied.
The remaining hypotheses are numerical caps and geometric admissibility. -/
theorem uniform_actual_nonexceptional_bound
    (Holes : ℕ) (W : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH B ε δ lo hi κ Lradius Cr εg : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hB : 0≤B)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hLradius : 0≤Lradius) (hCr : 0<Cr) (hεg : 0<εg)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp Cg : ℝ,0<Cs ∧ 0<Cp ∧ 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀R seed : Id,R≠0 → (R.absNorm:ℝ)≤Z^BR → Squarefree seed →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      ((∏I∈holes H,I).absNorm:ℝ)≤Z^BH → (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
    let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
    let S := finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    let β := originalColumn (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
    let Hsource := sourceNormCap (fun i=>Z^(w i)) b (X₁*X₂) d
    let volume := X₁*X₂*∏i,Z^(w i)
    let A := Cs*diagonalControl ballProfile*(sourceControl control W₁*sourceControl control W₂)^2*
      (sourceHeight t V t₁ t₂)^degree
    Hsource≤Z^B →
    ∀(η : Character)(tp K Wblock Tsec ξ : ℝ)(m : O)(χ₀ : RayCharacter),
      0<K → 0<Wblock → m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      frequencyRadius Tsec Z ξ≤Cr*Z^Lradius →
    ∀ρ : (p : ActiveLabel S β)→(U : Finset (CommonIndex p.val.1 p.val.2))→
      SourceBlocks p.val.1 p.val.2 U (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource→ℝ,
    (∀p∈liveLabels η S β,∀U,∀n : SourceBlocks p.val.1 p.val.2 U
        (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource,
      physicalBlock η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))≠0 →
      Real.logb Z (frequencyRadius Tsec Z ξ)+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤ρ p U n ∧
        ρ p U n≤Mcap) →
      ‖localizedDensity Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
          (fun I : supportedColumns S=>β I*heightCoeff η tp I) K Wblock
          (retainedWeight (frequencyRadius Tsec Z ξ))-
        partEnergy true η χ₀ Q m tp S β ballProfile (16*K*Wblock^4) Tsec Z ξ Hsource/(Wblock:ℂ)‖ ≤
      closedBudget (Fintype.card α) degree Cp Cg Z (κ*(∑i,w i)+ε+δ+εg)
        A b volume tp Wblock η seed d := by
  obtain ⟨degree,control,hr⟩ := uniform_actual_retained_nonexceptional (α:=α) M Hray hHray
    Holes W a b Mcap L Lslot Lcap Cap BR BH B ε δ lo hi κ
    hWs hW ha haUpper hb hM hLslot hLcap hCap hBR hBH hB hCapb hLordinary hε hδ
    hβ hκ Q hQt hQ72 hQM
  obtain ⟨Cg,hCg,hg⟩ := uniform_fourth_retained_geometry B Lradius Cr εg hB hLradius hCr hεg
  refine ⟨degree,control,?_⟩
  intro η₀ hQη
  obtain ⟨Cs,Cp,hCs,hCp,hr⟩ := hr η₀ hQη
  refine ⟨Cs,Cp,Cg,hCs,hCp,hCg,?_⟩
  filter_upwards [hr,hg] with Z hZ hgZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ R seed hR hRN hseed H hH hholes hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
    pool S β Hsource volume A hsourcecap η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2
    hradius ρ hgeometry
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hvolume : 0<volume := mul_pos (mul_pos hX₁ hX₂)
    (Finset.prod_pos (fun i _=>Real.rpow_pos_of_pos hZ0 (w i)))
  have hA : 0≤A := by
    have hdiag := diagonalControl_nonneg ballProfile
    have hheight := sourceHeight_one_le t V t₁ t₂ hV
    dsimp only [A]
    positivity
  have hHsource : 0≤Hsource := by
    have hp := (pairNorm_pos hd.1 hd.2).le
    change 0≤b^2*((X₁*X₂)/pairNorm d)*(∏i,2*Z^(w i))
    positivity
  have hcolumns (I : Id) (hi : β I≠0) : (I.absNorm:ℝ)≤Hsource :=
    (MixedOriginalNormCap.original_column_norm (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      W hWs σ freq (fun i=>Z^(w i)) (fun _=>Real.rpow_pos_of_pos hZ0 _)
      W₁ W₂ a b ha hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hXY I hi).2
  have hseedcolumn (I : Id) (_hI : I∈S) (hi : β I≠0) : seed∣I :=
    (original_nonzero_masks (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ I hi).2
  have hrZ := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
    R seed hR hRN hseed H hH hholes hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd hsourcecap
    η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 ρ hgeometry
  have hg' := hgZ seed hseed hseed.ne_zero η tp S β ballProfile hseedcolumn K Wblock
    (frequencyRadius Tsec Z ξ) Hsource hK hWblock hHsource hradius hsourcecap hcolumns Q m χ₀
  let F := analyticBudget degree Cp Z δ volume A (κ*(∑i,w i)+ε) tp d
  have hF : 0≤F := by
    have hp := (pairNorm_pos hd.1 hd.2).le
    have hh := (heightEnvelope_pos tp).le
    dsimp only [F,analyticBudget]
    positivity
  apply hrZ.trans
  calc
    _ = F*(fullRetainedGeometry η tp S β ballProfile (16*K*Wblock^4)
        (frequencyRadius Tsec Z ξ) Hsource Q m χ₀/Wblock) := by ring
    _ ≤ F*((4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource)*
        (Cg*Z^εg/(seed.absNorm:ℝ))/Wblock) := mul_le_mul_of_nonneg_left hg' hF
    _ = _ := by
      have hHs : Hsource=b^2*(2:ℝ)^(Fintype.card α)*volume/pairNorm d :=
        sourceNormCap_eq_volume (fun i=>Z^(w i)) b (X₁*X₂) d
      rw [hHs]
      dsimp only [F,analyticBudget,closedBudget]
      simp only [Real.rpow_add hZ0]
      have hseedN : (seed.absNorm:ℝ)≠0 := by
        exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero
      field_simp [(pairNorm_pos hd.1 hd.2).ne',hWblock.ne',hseedN]
      <;> ring

end
end Candidate.FourthPower.MixedActualNonexceptionalBound
