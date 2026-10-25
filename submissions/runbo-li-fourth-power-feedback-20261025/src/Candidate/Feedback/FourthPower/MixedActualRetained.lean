/- Copyright (c) 2026 Sil. Apache-2.0.
exact retained nonexceptional aggregation for originalColumn.
The actual child-envelope geometry is summed over all actual blocks.
Source estimates are supplied by MixedActualEnvelopePhysical, not assumed.
The localized scale 16*K*Wblock^4 and outer 1/Wblock are unchanged.
-/
import Candidate.Feedback.FourthPower.MixedActualGeometry
import Candidate.Feedback.FourthPower.MixedLocalizedDictionary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedActualRetained
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open RayFourExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows MixedCanonicalSource MixedHeightEnergy
open MixedHeightEnvelope MixedRawEnvelope MixedActualEnvelopePhysical MixedLocalizedDictionary
open MixedActualGeometry CenteredMomentSecondBlockHarmonicMass
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

/-- Common analytic factor, including the raw source volume and the
ordinary prefix denominator. Independent of actual label and block. -/
def analyticBudget (degree : ℕ) (Cp Z δ volume A base tp : ℝ) (d : Id×Id) : ℝ :=
  volume*(Cp*Z^δ*(A/pairNorm d)*Z^base*
    heightEnvelope tp^(2*degree)*profileMoment degree^2)

/-- The actual retained-label subsum with zero physical blocks removed. -/
def retainedLiveGeometry (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (Ψ : 𝓢(ℝ,ℂ)) (K radius Hsource : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) : ℝ :=
  ∑p∈liveLabels η S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
    ∑n : SourceBlocks p.val.1 p.val.2 U K radius Hsource,
      liveChildGeometry η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U radius
        (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ K (fun i=>(n i:ℤ))

/-- Extending the retained-label subsum introduces only nonnegative
terms. The full sum is exactly the one controlled by generic harmonic mass. -/
theorem retainedLiveGeometry_le_full (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (Ψ : 𝓢(ℝ,ℂ)) (K radius Hsource : ℝ) (hK : 0≤K) (Q : Id) (m : O)
    (χ₀ : RayCharacter) :
    retainedLiveGeometry η tp S β Ψ K radius Hsource Q m χ₀≤
      fullRetainedGeometry η tp S β Ψ K radius Hsource Q m χ₀ := by
  unfold retainedLiveGeometry fullRetainedGeometry
  rw [Fintype.sum_sigma,Fintype.sum_sigma]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro p _hp _hnot
  apply Finset.sum_nonneg
  intro U _hU
  apply Finset.sum_nonneg
  intro n _hn
  exact liveChildGeometry_nonneg η tp S β p.val.1 p.val.2
    (commonLabels_supported (activeSource S β) _ _ p.property).1
    (commonLabels_supported (activeSource S β) _ _ p.property).2 U radius
    (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ K hK (fun i=>(n i:ℤ))
variable {α : Type*} [Fintype α]

/-- The finite upper support cap is a fixed profile/slot factor times
the actual volume, divided by the original pair of prefix norms. -/
theorem sourceNormCap_eq_volume (P : α→ℝ) (b T : ℝ) (d : Id×Id) :
    sourceNormCap P b T d =
      b^2*(2:ℝ)^(Fintype.card α)*(T*∏i,P i)/pairNorm d := by
  unfold sourceNormCap
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ]
  ring

local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- The localized retained density minus its EXACT exceptional part is
bounded by the common analytic factor times fullRetainedGeometry.
The latter has the proved generic harmonic bound in MixedActualGeometry.
This theorem supplies all analytic envelopes internally. -/
theorem uniform_actual_retained_nonexceptional
    (Holes : ℕ) (W : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH B ε δ lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hB : 0≤B)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp : ℝ,0<Cs ∧ 0<Cp ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
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
      (analyticBudget degree Cp Z δ volume A (κ*(∑i,w i)+ε) tp d)*
        fullRetainedGeometry η tp S β ballProfile (16*K*Wblock^4)
          (frequencyRadius Tsec Z ξ) Hsource Q m χ₀/Wblock := by
  obtain ⟨degree,control,hphysical⟩ := uniform_actual_child_envelope (α:=α) M Hray hHray
    Holes 1 W ballProfile a b Mcap L Lslot Lcap Cap BR BH B ε δ lo hi κ
    hWs hW ha haUpper hb hM hLslot hLcap hCap hBR hBH hB hCapb hLordinary hε hδ
    hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,control,?_⟩
  intro η₀ hQη
  obtain ⟨Cs,Cp,hCs,hCp,hphysical⟩ := hphysical η₀ hQη
  refine ⟨Cs,Cp,hCs,hCp,hphysical.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ R seed hR hRN hseed H hH hholes hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
    pool S β Hsource volume A hsourcecap η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 ρ hgeometry
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hK4 : 0<16*K*Wblock^4 := by positivity
  have hvolume : 0<volume := mul_pos (mul_pos hX₁ hX₂)
    (Finset.prod_pos (fun i _=>Real.rpow_pos_of_pos hZ0 (w i)))
  have hA : 0≤A := by
    have hdiag := diagonalControl_nonneg ballProfile
    have hheight := sourceHeight_one_le t V t₁ t₂ hV
    dsimp only [A]
    positivity
  let F := analyticBudget degree Cp Z δ volume A (κ*(∑i,w i)+ε) tp d
  have hF : 0≤F := by
    have hpair := (pairNorm_pos hd.1 hd.2).le
    have hheight := (heightEnvelope_pos tp).le
    dsimp only [F,analyticBudget]
    positivity
  have hcolumns (I : Id) (hi : β I≠0) : (I.absNorm:ℝ)≤Hsource :=
    (MixedOriginalNormCap.original_column_norm (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      W hWs σ freq (fun i=>Z^(w i)) (fun _=>Real.rpow_pos_of_pos hZ0 _)
      W₁ W₂ a b ha hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hXY I hi).2
  have hpoint := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
    R seed hR hRN hseed H hH hholes hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd hsourcecap
  have hpart : ‖partEnergy false η χ₀ Q m tp S β ballProfile (16*K*Wblock^4)
      Tsec Z ξ Hsource‖≤F*fullRetainedGeometry η tp S β ballProfile (16*K*Wblock^4)
        (frequencyRadius Tsec Z ξ) Hsource Q m χ₀ := by
    apply (partEnergy_norm_le false η χ₀ Q m tp S β ballProfile (16*K*Wblock^4)
      Tsec Z ξ Hsource).trans
    apply le_trans (b:=F*retainedLiveGeometry η tp S β ballProfile (16*K*Wblock^4)
      (frequencyRadius Tsec Z ξ) Hsource Q m χ₀)
    · unfold retainedLiveGeometry
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U _hU
      apply Finset.sum_le_sum
      intro n _hn
      have hsupp := commonLabels_supported (activeSource S β) _ _ p.property
      rw [←physicalBlock_active η tp S β p.val.1 p.val.2 hsupp.1 hsupp.2 U
        (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))]
      by_cases hzero : physicalBlock η tp S β p.val.1 p.val.2 hsupp.1 hsupp.2 U
          (frequencyRadius Tsec Z ξ)
          (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))=0
      · simp only [liveChildGeometry,if_pos hzero,mul_zero]
        rw [hzero,norm_zero]
      · obtain ⟨τ,_hf,hb⟩ := hpoint η p U
        obtain ⟨hg,hcap⟩ := hgeometry p hp U n hzero
        have hbound := hb tp (frequencyRadius Tsec Z ξ) (16*K*Wblock^4) (ρ p U n) m χ₀
          (fun i=>(n i:ℤ)) hK4 hm hml hm2 hzero hg hcap
        have he := childBlockBudget_normalized degree Cp Z δ volume A (κ*(∑i,w i)+ε)
          tp (16*K*Wblock^4) hZ0 hvolume hA d hd η p.val.1 p.val.2 hsupp.1 hsupp.2 U
          (fun i=>(n i:ℤ))
        have hnorm : childBlockBudget degree Cp Z δ volume A (κ*(∑i,w i)+ε)
            tp (16*K*Wblock^4) d η p.val.1 p.val.2 U (fun i=>(n i:ℤ)) =
            F*childGeometry η p.val.1 p.val.2 U (16*K*Wblock^4) (fun i=>(n i:ℤ)) := by
          calc
            _ = (childBlockBudget degree Cp Z δ volume A (κ*(∑i,w i)+ε)
              tp (16*K*Wblock^4) d η p.val.1 p.val.2 U (fun i=>(n i:ℤ))/volume)*volume :=
                (div_mul_cancel₀ _ hvolume.ne').symm
            _ = _ := by rw [he];dsimp only [F,analyticBudget];ring
        have hb' : ‖physicalBlock η tp S β p.val.1 p.val.2 hsupp.1 hsupp.2 U
            (frequencyRadius Tsec Z ξ)
            (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
            ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))‖≤
            childBlockBudget degree Cp Z δ volume A (κ*(∑i,w i)+ε)
              tp (16*K*Wblock^4) d η p.val.1 p.val.2 U (fun i=>(n i:ℤ)) := by
          simpa only [childBlockBudget,pow_one] using hbound
        rw [hnorm] at hb'
        simpa only [liveChildGeometry,if_neg hzero] using hb'
    · exact mul_le_mul_of_nonneg_left
        (retainedLiveGeometry_le_full η tp S β ballProfile (16*K*Wblock^4)
          (frequencyRadius Tsec Z ξ) Hsource hK4.le Q m χ₀) hF
  rw [source_retained_split η χ₀ Q m tp S β K Wblock Tsec Z ξ Hsource hK hWblock
    (fun I _ hi=>hcolumns I hi),add_div,add_sub_cancel_left,norm_div,
    Complex.norm_real,Real.norm_of_nonneg hWblock.le]
  exact div_le_div_of_nonneg_right hpart hWblock.le

end
end Candidate.Feedback.FourthPower.MixedActualRetained
