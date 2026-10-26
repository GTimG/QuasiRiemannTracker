/- Copyright (c) 2026 Sil. Apache-2.0.
The actual allocated live source after genuine common extraction.
Both the genuine common norm and every artificial selected norm survive
the return to the original global normalization.
-/
import Candidate.FourthPower.MixedUniformAllocated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedCommonAllocated
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedLiteralAllocation MixedUniformAllocated MixedFrozenSource
open MixedLiveNormalization MixedLiveRows MixedTupleRows NativeInjectiveEnergy NativeFiniteHoles
open MixedCommonCoefficient MixedCommonRestriction
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentFirstSectors
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

def allocatedLiveSum (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (G R D : Id)
    (allocation : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)))
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑v∈liveBox (sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B hB,
    tupleWeight (punctureProduct S H) v*allocationTerm D Finset.univ v allocation*
      liveProfile B G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v*
      idealCoeff χ (finiteTupleProduct v)

theorem allocated_live_row (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (G R D : Id)
    (allocation : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)))
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*
      allocatedLiveSum χ S H pool d hd B hB G R D allocation ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
    allocatedRow χ S H (fun i : liveIndices B=>pool i.val)
      (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
      ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩ D (R*G) allocation
      (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  unfold allocatedLiveSum sourcePools
  rw [source_live_box pool d hd (plainSupportPool b X₁ Y₁) (plainSupportPool b X₂ Y₂) B hB]
  unfold allocatedRow sourcePools liveProfile
  apply congrArg (fun x : ℂ=>normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*x)
  apply Finset.sum_congr
  · ext v;simp only [Fintype.mem_piFinset]
  · intro v hv;rfl

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem uniform_common_allocated_source
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
    ∀R G F : Id,R≠0 → G≠0 → F≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*F)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀B : Tuple α,∀hB : ∀j,B j≠0,
      finiteTupleProduct B=G → (∀i : liveIndices B,∀P∈H,P.val∈R₀ i.val) →
    ∀D : Id,D∣F → ∀allocation : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)),
      radialEnergy (fun z=>normalization (X₁*X₂) (fun i=>Z^(w i))*
        (frozenCoefficient B G R
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))*
        allocatedLiveSum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
          (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B hB G R D allocation
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C*(F.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/
        ((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ))*
        diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i : selectedLive D allocation,w i.val.val)+ε) := by
  obtain ⟨K,hK,hslot⟩ := slot_profile_bound W hW.continuous hWs lo hi
  let A : ℝ := (∏_i : α,K)^2*2^Fintype.card α
  have hA : 0<A := by
    have hKpos : 0<K := zero_lt_one.trans_le hK
    dsimp [A]
    positivity
  obtain ⟨degree,S,hbase⟩ := uniform_allocated_subsets (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hδ hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C*A,mul_pos hC hA,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R G F hR hG hF H hH hcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    d hd B hB hprod hHR D hDF allocation
  let ν := slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
  let Wslot := fun i=>slotProfile W (σ i) (freq i)
  let P := fun i=>Z^(w i)
  let E := (C*(F.absNorm:ℝ)^δ/((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ))*
    diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i : selectedLive D allocation,w i.val.val)+ε)
  have hE : 0≤E := by
    have := diagonalControl_nonneg s.radial.profile
    have hZ0 : 0<Z := zero_lt_one.trans hZ.1
    dsimp [E]
    positivity
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    (R*G) F (mul_ne_zero hR hG) hF H hH hcap W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
    ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩ (liveIndices B) hHR D hDF allocation
  have hchild : radialEnergy (fun z=>normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*
      allocatedLiveSum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB G R D allocation ν Wslot P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        E/pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)) := by
    simp_rw [allocated_live_row]
    apply he.trans_eq
    dsimp only [E]
    ring
  have hh := frozen_source_energy B hB G R hG hprod d hd (X₁*X₂) (mul_pos hX₁ hX₂)
    ν Wslot P (fun _=>K) (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
    (fun i I=>slot_coefficient_norm _ R₀ t i I)
    (fun i x=>hslot (σ i) (freq i) (hσ i) (hσhi i) x) (fun _=>hK) 1 2 (by norm_num)
    (fun i=>(slot_profile_support W (σ i) (freq i)).trans hWs) _
    (effectiveState s).radial.keep s.radial.profile s.radial.scale E hE hchild
  apply hh.trans_eq
  dsimp only [E,A]
  norm_num only [max_eq_right (show (1:ℝ)≤2 by norm_num)]
  ring

end
end Candidate.FourthPower.MixedCommonAllocated
