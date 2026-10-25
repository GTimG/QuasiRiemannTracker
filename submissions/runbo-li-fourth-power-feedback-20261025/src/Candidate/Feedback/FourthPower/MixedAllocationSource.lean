/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform analytic bound for whole finite sums of literal frozen sources.
Constants precede the allocation family and all original parameters.
The exact live weights, zero allocations and divisor norms are retained.
-/
import Candidate.Feedback.FourthPower.MixedAllocationCost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedAllocationSource
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedFrozenSource MixedLiveNormalization MixedAllocationCost
open MixedCommonCoefficient NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentFirstSectors
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

def frozenRow (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (F R : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  normalization (X₁*X₂) P*(frozenCoefficient B (finiteTupleProduct B) R ν Wslot P*
    liveSum χ S H pool d hd B hB F R ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂)

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- There is no child-energy hypothesis: the actual canonical estimate
is supplied by uniform_live_source before summing the allocation family. -/
theorem uniform_frozen_sum
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R F : Id,R≠0 → F≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport (R*F)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀labels : Finset (Tuple α),
    ∀hlabels : ∀B : labels,∀j,B.val j≠0,
    ∀active : labels→Prop,∀phase : labels→O→ℂ,
      (∀B z,(effectiveState s).radial.keep z→‖phase B z‖≤1) →
      (∀B,¬active B→∀z,phase B z=0) →
      (∀B : labels,active B→∀i : liveIndices B.val,∀P∈H,P.val∈R₀ i.val) →
      radialEnergy (fun z=>∑B : labels,phase B z*
        frozenRow (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
          (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B.val (hlabels B) F R
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C/pairNorm d)*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+ε)*budget labels active Z κ w := by
  obtain ⟨degree,S,hbase⟩ := uniform_live_source (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R F hR hF H hH hcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    d hd labels hlabels active phase hphase hzero hHR
  let A := (C/pairNorm d)*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+ε)
  let f := fun (B : labels)(z : O)=>frozenRow (naturalCharacter s.character z)
    (enclosure (Cap*Z^Lcap)) H (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
    d hd B.val (hlabels B) F R
    (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
  have hf (B : labels) (hB : active B) :
      radialEnergy (f B) (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        A*liveWeight Z κ w B.val := by
    have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
      R F hR hF H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B.val (hlabels B) (hHR B hB)
    apply he.trans_eq
    rw [show s.width+κ*(∑i : liveIndices B.val,w i.val)+ε=
        s.width+ε+κ*(∑i : liveIndices B.val,w i.val) by ring,
      Real.rpow_add (zero_lt_one.trans hZ.1)]
    dsimp only [A,liveWeight]
    ring
  have he := radial_active_family active phase f (fun B=>A*liveWeight Z κ w B.val)
    (effectiveState s).radial.keep s.radial.profile s.radial.scale radial
    s.radial.scale_pos s.radial_support s.radial.nonneg hphase hzero hf
  apply he.trans_eq
  rw [Fintype.card_coe]
  have hsum : (∑B : labels,if active B then A*liveWeight Z κ w B.val else 0)=
      A*∑B : labels,if active B then liveWeight Z κ w B.val else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    split_ifs <;> ring
  rw [hsum]
  change _=A*budget labels active Z κ w
  unfold budget
  ring

end
end Candidate.Feedback.FourthPower.MixedAllocationSource
