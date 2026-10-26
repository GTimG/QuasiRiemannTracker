/- Copyright (c) 2026 Sil. Apache-2.0.
retains the actual childEnvelope in both raw budgets. The number rho is used only to check canonical-state admissibility. Actual second nonexceptional physical block for the literal
tuple-weighted originalColumn. Both analytic source envelopes are proved
by MixedCanonicalEnvelope. The independent first supplier identity is
outside this theorem; no equality identifying that first beta is assumed.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedActualFamily
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedPhysicalEnvelopes
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedActualEnvelopePhysical
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open RayFourExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows MixedCanonicalSource MixedHeightEnergy
open MixedHeightEnvelope MixedRawEnvelope MixedCanonicalEnvelope MixedActualFamily
open MixedOriginalNormCap MixedOriginalCoprimality MixedPhysicalEnvelopes MixedLiteralAllocation
open NativeInjectiveEnergy
open CenteredMomentEnergyChildState CenteredMomentEnergyState
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSectors CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondHeightFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentSecondWindowBudget
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondWholeKernel
open CenteredMomentSecondNonexceptionalScalar
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Monotonicity in the literal conductor-times-scale cost. No exponent
majorant is substituted for this cost. -/
theorem raw_cost_mono (volume A Z exponent cost cost' : ℝ)
    (hvolume : 0≤volume) (hA : 0≤A) (hZ : 0<Z) (hcost : cost≤cost')
    (G : Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) :
    rawBudget volume (A*cost) Z exponent G d≤
      rawBudget volume (A*cost') Z exponent G d := by
  let F := volume*A*Z^exponent/(G.absNorm:ℝ)/pairNorm d
  have hF : 0≤F := by
    have hpair := (pairNorm_pos hd.1 hd.2).le
    dsimp only [F]
    positivity
  calc
    _ = F*cost := by dsimp only [F,rawBudget];ring
    _ ≤ F*cost' := mul_le_mul_of_nonneg_left hcost hF
    _ = _ := by dsimp only [F,rawBudget];ring
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Concrete nonzero-block bound. Only compact-profile, finite-hole,
full-norm, seed and geometric hypotheses remain. In particular neither
left nor right source energy is a premise. Constants precede all original
profiles, heights, labels, blocks and Fourier variables. The two raw
budgets retain 1/N(Gleft), 1/N(Gright), and 1/pairNorm(d). -/
theorem uniform_actual_child_envelope
    (Holes decay : ℕ) (W : ℝ→ℂ) (Ψ : 𝓢(ℝ,ℂ))
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
    ∀(η : Character)(p : ActiveLabel S β)(U : Finset (CommonIndex p.val.1 p.val.2)),
    ∃τ : RayCharacter→Character,
    Family η p.val.1 p.val.2
      (commonLabels_supported (activeSource S β) _ _ p.property).1
      (commonLabels_supported (activeSource S β) _ _ p.property).2 U τ ∧
    ∀(tp radius Kphys ρ : ℝ)(m : O)(χ₀ : RayCharacter)(n : Fin 4→ℤ),0<Kphys →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      physicalBlock η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U radius
        (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ Kphys n≠0 →
      Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤ρ → ρ≤Mcap →
      ‖physicalBlock η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U radius
        (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ Kphys n‖ ≤
      Cp*Z^δ*(outerScalar p.val.1 p.val.2 Kphys n*normalizer p.val.1 p.val.2 U)*
        (windowBudget degree tp (rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (κ*(∑i,w i)+ε) p.val.1 d)*
          windowBudget degree tp (rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (κ*(∑i,w i)+ε) p.val.2 d))/
        (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  obtain ⟨degree,control,hsource⟩ := uniform_canonical_source_envelope (α:=α) M Hray hHray
    Holes W a b Mcap L Lslot Lcap Cap ((BR+B)+B+BH) B ε lo hi κ
    hWs hW ha haUpper hb hM hLslot hLcap hCap (by positivity) hB hCapb hLordinary
    hε hβ hκ Q hQt hQ72 hQM
  obtain ⟨Cp,hCp,hphysical⟩ := actual_canonical_source_envelopes Ψ decay degree degree B δ hB hδ
  refine ⟨degree,control,?_⟩
  intro η₀ hQη
  obtain ⟨Cs,hCs,hsource⟩ := hsource η₀ hQη
  refine ⟨Cs,Cp,hCs,hCp,?_⟩
  filter_upwards [hsource,hphysical] with Z hsourceZ hphysicalZ
  refine ⟨hsourceZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ R seed hR hRN hseed H hH hholes hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
    pool S β Hsource volume A hsourcecap η p U
  have hZ0 : 0<Z := zero_lt_one.trans hsourceZ.1
  have hP : ∀i,0<Z^(w i) := fun _=>Real.rpow_pos_of_pos hZ0 _
  have hvolume : 0<volume := mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hA : 0≤A := by
    have hdiag := diagonalControl_nonneg ballProfile
    have hheight := sourceHeight_one_le t V t₁ t₂ hV
    dsimp only [A]
    positivity
  have hHsource : 0≤Hsource := by
    have hpair := (pairNorm_pos hd.1 hd.2).le
    change 0≤b^2*((X₁*X₂)/pairNorm d)*(∏i,2*Z^(w i))
    positivity
  have hcolumns (I : Id) (hi : β I≠0) : (I.absNorm:ℝ)≤Hsource :=
    (MixedOriginalNormCap.original_column_norm (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      W hWs σ freq (fun i=>Z^(w i)) hP W₁ W₂ a b ha hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hXY I hi).2
  have hsupp := commonLabels_supported (activeSource S β) _ _ p.property
  have hseedp := original_active_common_seed (enclosure (Cap*Z^Lcap)) H pool d hd R seed
    (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ S hseed p
  obtain ⟨τall,hτall⟩ := exists_actual_families η S β
  let τ := τall p U
  have hf := hτall p U
  refine ⟨τ,hf,?_⟩
  intro tp radius Kphys ρ m χ₀ n hKphys hm hml hm2 hne hledger hρ
  let rows := partRows false η χ₀ Q m p.val.1 p.val.2 U radius
  have hgeometry (χ : RayCharacter) := actual_canonical_geometry hf tp S β radius rows Ψ Kphys
    hKphys n hne Z BR ρ hsourceZ.1 χ Q R hR hRN hledger
  have hcost (χ : RayCharacter) :
      ((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤childEnvelope η p.val.1 p.val.2 U n :=
    family_child_envelope hf tp S β radius rows Ψ Kphys hKphys n hne χ
  have hchild : 0≤childEnvelope η p.val.1 p.val.2 U n := by
    have hdyad := (dyadicScale_pos (n 1)).le
    unfold childEnvelope
    positivity
  have hnormone : (1:ℝ)≤(p.val.2.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsupp.2.1)
  have hdivision : Hsource/(p.val.2.absNorm:ℝ)≤Z^B :=
    (div_le_self hHsource hnormone).trans hsourcecap
  have hbudget (G : Id) : 0≤rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (κ*(∑i,w i)+ε) G d := by
    have hpair := (pairNorm_pos hd.1 hd.2).le
    unfold rawBudget
    positivity
  apply hphysicalZ.2 Kphys hKphys n η τ tp S β p.val.1 p.val.2 hsupp.1 hsupp.2
    (active_equal_support S β p) U hf Hsource hcolumns hdivision radius Q m χ₀ hQ72 hm hml hm2
    (rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (κ*(∑i,w i)+ε) p.val.1 d)
    (rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (κ*(∑i,w i)+ε) p.val.2 d)
    (hbudget p.val.1) (hbudget p.val.2)
  all_goals
    intro L2 _hL2 hL2N hL2 χ v
    have hcaps := active_mask_caps S β p Hsource Z B BR BH hHsource hZ0
      (fun I _ hi=>hcolumns I hi) hsourcecap R L2 hR hL2 hRN hL2N H hholes
  · have he := hsourceZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
      BR (τ χ) n (hgeometry χ).1 ((hgeometry χ).2.trans hρ)
      R p.val.1 seed L2 hR hRN hsupp.1.1 hseedp.1 hL2 hcaps.1 hcaps.2.2.1
      H hH hcaps.2.2.2.2.1 hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
    have hb := raw_cost_mono volume A Z (κ*(∑i,w i)+ε)
      (((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)) (childEnvelope η p.val.1 p.val.2 U n) hvolume.le hA hZ0 (hcost χ) p.val.1 d hd
    have hb' := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hb (Nat.cast_nonneg L2.absNorm)) (by positivity : 0≤(1+‖v‖)^(2*degree))
    apply he.trans
    simpa only [A,volume,mul_assoc,add_assoc] using hb'
  · have he := hsourceZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
      BR (τ χ) n (hgeometry χ).1 ((hgeometry χ).2.trans hρ)
      R p.val.2 seed L2 hR hRN hsupp.2.1 hseedp.2 hL2 hcaps.2.1 hcaps.2.2.1
      H hH hcaps.2.2.2.2.2 hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
    have hb := raw_cost_mono volume A Z (κ*(∑i,w i)+ε)
      (((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)) (childEnvelope η p.val.1 p.val.2 U n) hvolume.le hA hZ0 (hcost χ) p.val.2 d hd
    have hb' := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hb (Nat.cast_nonneg L2.absNorm)) (by positivity : 0≤(1+‖v‖)^(2*degree))
    apply he.trans
    simpa only [A,volume,mul_assoc,add_assoc] using hb'

end
end Candidate.FourthPower.MixedActualEnvelopePhysical

