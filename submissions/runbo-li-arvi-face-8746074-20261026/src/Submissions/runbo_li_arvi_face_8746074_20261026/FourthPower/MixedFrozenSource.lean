/- Copyright (c) 2026 Sil. Apache-2.0.
The uniform canonical estimate on the literal live allocation, including
its frozen coefficient and original global normalization.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedUniformSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFrozenSource
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedUniformSource MixedLiveRows MixedLiveNormalization NativeInjectiveEnergy
open MixedTupleRows MixedCommonCoefficient MixedCommonRestriction NativeFiniteHoles
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic HeckePrimeAnnular CenteredMomentCommonMaskEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentFirstSectors
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

def liveSum (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (F R : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑v∈liveBox (pools pool (residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁))
      (residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂))) B hB,
    tupleWeight (punctureProduct S H) v*
      liveProfile B F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v*
      idealCoeff χ (finiteTupleProduct v)

theorem live_sum_eq_source (χ : Character) (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple α) (hB : ∀j,B j≠0) (F R : Id)
    (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    liveSum χ S H pool d hd B hB F R ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      source χ S H (R*F) (fun i : liveIndices B=>pool i.val)
        (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val)
        W₁ W₂ b X₁ X₂ Y₁ Y₂ (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)) := by
  unfold liveSum
  rw [source_live_box pool d hd (plainSupportPool b X₁ Y₁) (plainSupportPool b X₂ Y₂) B hB]
  simp_rw [residual_plain_pool]
  unfold source liveProfile
  apply Finset.sum_congr
  · ext v;simp only [Fintype.mem_piFinset]
  · intro v hv;rfl

omit [Fintype α] in
theorem slot_coefficient_norm (ν : α→Character) (R₀ : α→Finset Id) (t : ℝ) (i : α) (I : Id) :
    ‖slotCoefficient ν R₀ t i I‖≤1 := by
  by_cases hI : I=0
  · subst I
    unfold slotCoefficient heightCoefficient holeCoefficient
    simp only [map_zero]
    split_ifs <;> simp only [zero_mul,norm_zero,zero_le_one]
  · rw [slotCoefficient,heightCoefficient_norm _ _ I hI]
    unfold holeCoefficient
    split_ifs
    · simp only [norm_zero,zero_le_one]
    · exact idealCoeff_norm_le_one _ _

theorem slot_profile_support (W : ℝ→ℂ) (σ freq : ℝ) :
    Function.support (slotProfile W σ freq)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp only [slotProfile,hw,zero_mul])

theorem slot_profile_bound (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (lo hi : ℝ) :
    ∃K : ℝ,1≤K ∧ ∀σ freq : ℝ,lo≤σ → σ≤hi → ∀x,‖slotProfile W σ freq x‖≤K := by
  obtain ⟨K,hK,hbound⟩ := fixed_profile_norm_bound W hW 1 2 lo hi (by norm_num)
  refine ⟨max 1 K,le_max_left _ _,?_⟩
  intro σ freq hσlo hσhi x
  by_cases hx : W x=0
  · simp only [slotProfile,hx,zero_mul,norm_zero]
    exact zero_le_one.trans (le_max_left _ _)
  · have hs := hWs hx
    rw [slotProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hs.1)]
    simp only [Complex.neg_re,shift_re]
    exact (hbound σ ⟨hσlo,hσhi⟩ x hs).trans (le_max_right _ _)

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- The constant precedes the actual allocation, all extracted ideals,
and both ordinary profiles. This supplies the canonical child energy,
rather than leaving it as an assumption of the normalization theorem. -/
theorem uniform_live_source
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
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀B : Tuple α,∀hB : ∀j,B j≠0,
      (∀i : liveIndices B,∀P∈H,P.val∈R₀ i.val) →
      radialEnergy (fun z=>normalization (X₁*X₂) (fun i=>Z^(w i))*
        (frozenCoefficient B (finiteTupleProduct B) R
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))*
        liveSum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
          (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B hB F R
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C/((finiteTupleProduct B).absNorm:ℝ)/pairNorm d)*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i : liveIndices B,w i.val)+ε) := by
  obtain ⟨K,hK,hslot⟩ := slot_profile_bound W hW.continuous hWs lo hi
  let A : ℝ := (∏_i : α,K)^2*2^Fintype.card α
  have hA : 0<A := by
    have hKpos : 0<K := zero_lt_one.trans_le hK
    dsimp [A]
    positivity
  obtain ⟨degree,S,hbase⟩ := uniform_source (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C*A,mul_pos hC hA,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R F hR hF H hH hcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B hB hHR
  let ν := slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
  let Wslot := fun i=>slotProfile W (σ i) (freq i)
  let P := fun i=>Z^(w i)
  let E := C*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i : liveIndices B,w i.val)+ε)
  have hE : 0≤E := by
    have := diagonalControl_nonneg s.radial.profile
    have hZ0 : 0<Z := zero_lt_one.trans hZ.1
    dsimp [E]
    positivity
  have hPB : finiteTupleProduct B≠0 := Finset.prod_ne_zero_iff.mpr (fun j _=>hB j)
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    (R*F) (mul_ne_zero hR hF) H hH hcap W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
    (mul_ne_zero hd.1 (hB _)) (mul_ne_zero hd.2 (hB _)) (liveIndices B) hHR
  have hchild : radialEnergy (fun z=>normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*
      liveSum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB F R ν Wslot P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        E/pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)) := by
    simp_rw [live_sum_eq_source]
    apply he.trans_eq
    dsimp [E]
    ring
  have hh := frozen_source_energy B hB (finiteTupleProduct B) R hPB rfl d hd (X₁*X₂)
    (mul_pos hX₁ hX₂) ν Wslot P (fun _=>K) (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
    (fun i I=>slot_coefficient_norm _ R₀ t i I)
    (fun i x=>hslot (σ i) (freq i) (hσ i) (hσhi i) x) (fun _=>hK) 1 2 (by norm_num)
    (fun i=>(slot_profile_support W (σ i) (freq i)).trans hWs) _
    (effectiveState s).radial.keep s.radial.profile s.radial.scale E hE hchild
  apply hh.trans_eq
  dsimp only [E,A]
  norm_num only [max_eq_right (show (1:ℝ)≤2 by norm_num)]
  ring

end
end Candidate.FourthPower.MixedFrozenSource
