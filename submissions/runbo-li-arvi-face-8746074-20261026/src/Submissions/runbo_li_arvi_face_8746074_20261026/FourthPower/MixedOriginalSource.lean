/- Copyright (c) 2026 Sil. Apache-2.0.
Apply the proved common-row estimate to the actual original restricted
column source. The displayed coefficient has its original seed, tuple
restriction, common coprimality mask, and squarefree divisor mask.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedRestrictedDictionary
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedCommonSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedOriginalSource
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedCommonSource MixedRestrictedDictionary MixedLiveNormalization MixedSourceAssembly
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

/-- The original residual-column source, before genuine common
extraction. This includes the full original normalization. -/
def originalMaskedRow (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  normalization (X₁*X₂) P*
    ∑I∈residualPool G hG (finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))),
      (if IsCoprime G I ∧ D∣I then finiteColumnCoefficient
        (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
        (fun v=>tupleWeight (punctureProduct S H) v*profileCoefficient R ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ d.1 d.2 seed v) (G*I) else 0)*idealCoeff χ I

/-- Exact dictionary; the seed may be removed from the live profile only
because it divides the already extracted genuine common ideal G. -/
theorem original_masked_row_eq (χ : Character) (S H : Finset PrimeIdeal)
    (pool : α→Finset Id) (hp : ∀i,∀I∈pool i,Prime I)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (G R seed D : Id) (hG : G≠0) (hseed : seed∣G)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    originalMaskedRow χ S H pool d hd G R seed D hG ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      commonMaskedRow χ S H pool d hd G R D ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ :=
  normalized_common_masked_identity χ S H pool hp d hd G R seed D hG hseed
    ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Uniform estimate for the actual original restricted-column source,
with the constants chosen before the original data. There is no analytic
child-energy premise. An independent column-height phase is deliberately
handled in the separate height dictionary rather than discarded here. -/
theorem uniform_original_source
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R G seed D : Id,R≠0 → ∀hG : G≠0,seed∣G → Squarefree D →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
      radialEnergy (fun z=>originalMaskedRow (naturalCharacter s.character z)
        (enclosure (Cap*Z^Lcap)) H (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
        d hd G R seed D hG
        (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
        (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C*(G.absNorm:ℝ)^δ*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))*
        diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  obtain ⟨degree,S,hbase⟩ := uniform_common_source (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hδ hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R G seed D hR hG hseed hD H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R G D hR hG hD H hH hcap hHR W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
  have hp (i : α) (I : Id) (hI : I∈supportedPool (primePool M Hray 2 (Z^(w i)))) : Prime I :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1
  apply (le_of_eq ?_).trans he
  apply congrArg (fun f : O→ℂ=>radialEnergy f
    (effectiveState s).radial.keep s.radial.profile s.radial.scale)
  funext z
  exact original_masked_row_eq (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
    (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) hp d hd G R seed D hG hseed
    (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂

end
end Candidate.FourthPower.MixedOriginalSource
