/- Copyright (c) 2026 Sil. Apache-2.0.
Native nonexceptional retained aggregation on the ORIGINAL avoided
source labels. Same second decomposition; all analytic blocks supplied.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallActivePhysical
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedActualRetained

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallRetained
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

theorem uniform_avoided_retained
    (Holes : ℕ) (Wslot : ℝ → ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi : ℝ)
    (hWs : Function.support Wslot⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hMcap : 0≤Mcap) (hε : 0<ε) (hδCount : 0<δCount) (hδPhys : 0<δPhys)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M)

 :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp : ℝ,0<Cs ∧ 0<Cp ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
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
      analyticBudget degree Cp Z δPhys (sourceVolume s) A base tp s.d*
        fullRetainedGeometry η tp Sco beta ballProfile (16*K*Wblock^4)
          (frequencyRadius Tsec Z ξ) Hsource Q m χ₀/Wblock := by
  obtain ⟨degree,control,hbase⟩ := uniform_active_avoided_physical (ι:=ι) M Hray hHray
    Holes 1 Wslot ballProfile a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi
    hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary hBR hBH hBnorm hMcap
    hε hδCount hδPhys hβ Q hQt hQ72 hQM
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  obtain ⟨Cs,Cp,hCs,hCp,hbase⟩ := hbase η₀ hQη₀
  refine ⟨Cs,Cp,hCs,hCp,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap cover u seed hseed hu
    Sco beta A base Hsource η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 Rdecl hgeometry
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hK4 : 0<16*K*Wblock^4 := by positivity
  have hvolume := sourceVolume_pos s
  have hA : 0≤A := by
    have hs := slot_cost_nonneg s
    have hd := diagonalControl_nonneg ballProfile
    have hh : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    dsimp only [A]
    positivity
  let F:=analyticBudget degree Cp Z δPhys (sourceVolume s) A base tp s.d
  have hF : 0≤F := by
    have hp := (pairNorm_pos s.hd.1 s.hd.2).le
    have hh := (heightEnvelope_pos tp).le
    dsimp only [F,analyticBudget]
    positivity
  have hcolumns (I : Id) (hi : beta I≠0) : (I.absNorm:ℝ)≤Hsource :=
    (original_coefficient_cap (avoidSource s u) ha seed I hi).2
  have hpoint := hZ.2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap cover u seed hseed hu
  have hpart :
      ‖partEnergy false η χ₀ Q m tp Sco beta ballProfile (16*K*Wblock^4)
        Tsec Z ξ Hsource‖≤
      F*fullRetainedGeometry η tp Sco beta ballProfile (16*K*Wblock^4)
        (frequencyRadius Tsec Z ξ) Hsource Q m χ₀ := by
    apply (partEnergy_norm_le false η χ₀ Q m tp Sco beta ballProfile (16*K*Wblock^4)
      Tsec Z ξ Hsource).trans
    apply le_trans (b:=F*retainedLiveGeometry η tp Sco beta ballProfile (16*K*Wblock^4)
      (frequencyRadius Tsec Z ξ) Hsource Q m χ₀)
    · unfold retainedLiveGeometry
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      have hsupp := commonLabels_supported (activeSource Sco beta) _ _ p.property
      rw [←physicalBlock_active η tp Sco beta p.val.1 p.val.2 hsupp.1 hsupp.2 U
        (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i => (n i:ℤ))]
      by_cases hzero : physicalBlock η tp Sco beta p.val.1 p.val.2 hsupp.1 hsupp.2 U
          (frequencyRadius Tsec Z ξ)
          (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          ballProfile (16*K*Wblock^4) (fun i => (n i:ℤ))=0
      · simp [liveChildGeometry, hzero]
      · obtain ⟨τ,hfamily,hbnd⟩ := hpoint η p U
        obtain ⟨hg,hcap⟩ := hgeometry p hp U n hzero
        have hb := hbnd tp (frequencyRadius Tsec Z ξ) (16*K*Wblock^4)
          (Rdecl p U n) m χ₀ (fun i => (n i:ℤ)) hK4 hm hml hm2 hzero hg hcap
        have he := childBlockBudget_normalized degree Cp Z δPhys (sourceVolume s) A base
          tp (16*K*Wblock^4) hz hvolume hA s.d s.hd η p.val.1 p.val.2 hsupp.1 hsupp.2 U
          (fun i => (n i:ℤ))
        have hnorm : childBlockBudget degree Cp Z δPhys (sourceVolume s) A base
            tp (16*K*Wblock^4) s.d η p.val.1 p.val.2 U (fun i => (n i:ℤ))=
            F*childGeometry η p.val.1 p.val.2 U (16*K*Wblock^4) (fun i => (n i:ℤ)) := by
          calc
            _=(childBlockBudget degree Cp Z δPhys (sourceVolume s) A base
                tp (16*K*Wblock^4) s.d η p.val.1 p.val.2 U (fun i => (n i:ℤ))/
                sourceVolume s)*sourceVolume s := (div_mul_cancel₀ _ hvolume.ne').symm
            _=_ := by rw [he];dsimp only [F,analyticBudget];ring
        have hb' : ‖physicalBlock η tp Sco beta p.val.1 p.val.2 hsupp.1 hsupp.2 U
            (frequencyRadius Tsec Z ξ)
            (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
            ballProfile (16*K*Wblock^4) (fun i => (n i:ℤ))‖≤
            childBlockBudget degree Cp Z δPhys (sourceVolume s) A base
              tp (16*K*Wblock^4) s.d η p.val.1 p.val.2 U (fun i => (n i:ℤ)) := by
          simpa only [childBlockBudget,pow_one] using hb
        rw [hnorm] at hb'
        simpa only [liveChildGeometry,if_neg hzero] using hb'
    · exact mul_le_mul_of_nonneg_left
        (retainedLiveGeometry_le_full η tp Sco beta ballProfile (16*K*Wblock^4)
          (frequencyRadius Tsec Z ξ) Hsource hK4.le Q m χ₀) hF
  rw [source_retained_split η χ₀ Q m tp Sco beta K Wblock Tsec Z ξ Hsource hK hWblock
    (fun I _ hi => hcolumns I hi),add_div,add_sub_cancel_left,norm_div,
    Complex.norm_real,Real.norm_of_nonneg hWblock.le]
  exact div_le_div_of_nonneg_right hpart hWblock.le

end
end Candidate.FourthPower.RepairedSmallRetained
