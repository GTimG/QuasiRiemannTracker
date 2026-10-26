/- Copyright (c) 2026 Sil. Apache-2.0.
The native retained remainder at the ORIGINAL positive Gauss scale K.
All active-label admissibility is proved from uniform arithmetic caps;
localization uses K/16 and W=1, without changing the actual cutoff.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallClosed
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedActualAdmissibility

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallOriginalScale
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
open CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondLocalization
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


open RepairedSmallClosed MixedActualAdmissibility
theorem uniform_original_scale_nonexceptional
    (Holes : ℕ) (Wslot : ℝ → ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi Lradius Cr εg Meta ζ : ℝ)
    (hWs : Function.support Wslot⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hMcap : 0≤Mcap) (hε : 0<ε) (hδCount : 0<δCount) (hδPhys : 0<δPhys)
    (hLradius : 0≤Lradius) (hCr : 0<Cr) (hεg : 0<εg)
    (hζ : 0<ζ) (hMready : Lradius+Meta+Bnorm+ζ≤Mcap)
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
    ∀(η : Character)(tp K Tsec ξ : ℝ)(m : O)(χ₀ : RayCharacter),
      0<K → (η.modulus.absNorm:ℝ)≤Z^Meta → m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      frequencyRadius Tsec Z ξ≤Cr*Z^Lradius →
      ‖secondRetainedEnergy η tp Sco beta ballProfile K Tsec Z ξ-
        partEnergy true η χ₀ Q m tp Sco beta ballProfile K Tsec Z ξ Hsource‖≤
      closedBudget (Fintype.card ι) degree Cp Cg Z (base+δPhys+εg)
        A b (sourceVolume s) tp 1 η seed s.d

 := by
  obtain ⟨degree,control,hbase⟩ := uniform_avoided_nonexceptional (ι:=ι) M Hray hHray
    Holes Wslot a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi Lradius Cr εg
    hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary hBR hBH hBnorm hMcap
    hε hδCount hδPhys hLradius hCr hεg hβ Q hQt hQ72 hQM
  have hadmissible := uniform_actual_admissibility Lradius Meta Bnorm Cr ζ Mcap hCr hζ hMready
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  obtain ⟨Cs,Cp,Cg,hCs,hCp,hCg,hbase⟩ := hbase η₀ hQη₀
  refine ⟨Cs,Cp,Cg,hCs,hCp,hCg,?_⟩
  filter_upwards [hbase,hadmissible] with Z hZ haZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap cover u seed hseed hu
    Sco beta A base Hsource η tp K Tsec ξ m χ₀ hK hη hm hml hm2 hradius
  have hscale : 16*(K/16)*(1:ℝ)^4=K := by ring
  have hret := hZ.2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap cover u seed hseed hu
    η tp (K/16) 1 Tsec ξ m χ₀ (by positivity) (by norm_num) hm hml hm2 hradius
  rw [source_retained η tp Sco beta (K/16) 1 Tsec Z ξ (by norm_num)] at hret
  simp only [hscale,Complex.ofReal_one,div_one] at hret
  apply hret (fun _ _ _ => Lradius+Meta+Bnorm+ζ)
  intro p hp U n hne
  have hcolumns (I : Id) (hI : I∈Sco) (hi : beta I≠0) : (I.absNorm:ℝ)≤Hsource :=
    (original_coefficient_cap (avoidSource s u) ha seed I hi).2
  exact haZ.2 η Sco beta Hsource hη hcolumns hsourcecap p U (frequencyRadius Tsec Z ξ)
    (actual_nonzero_radius_pos η tp Sco beta _ _ _ _ U _ _ _ _ _ hne) hradius

end
end Candidate.FourthPower.RepairedSmallOriginalScale
