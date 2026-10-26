/- Copyright (c) 2026 Sil. Apache-2.0.
Close the complete artificial allocation sum after genuine extraction.
The original squarefree divisibility mask is restored with its 1/N(D)
saving and only an arbitrarily small power loss.
-/
import Candidate.FourthPower.MixedDivisorMask

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedCommonMasked
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedCommonAllocated MixedDivisorMask MixedLiveNormalization MixedSourceAssembly
open NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentDivisorAllocation
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem uniform_common_masked_source
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
    ∀R G D : Id,R≠0 → G≠0 → Squarefree D → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀B : Tuple α,∀hB : ∀j,B j≠0,
      finiteTupleProduct B=G → (∀i : liveIndices B,∀P∈H,P.val∈R₀ i.val) →
      radialEnergy (fun z=>normalization (X₁*X₂) (fun i=>Z^(w i))*
        (frozenCoefficient B G R
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))*
        maskedLiveSum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
          (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B hB G R D
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      (C*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))*
        diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i : liveIndices B,w i.val)+ε) := by
  obtain ⟨degree,S,hbase⟩ := uniform_common_allocated_source (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε (δ/2) lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε (half_pos hδ) hβ hκ Q hQt hQ72 hQM
  obtain ⟨Ccount,hCcount,hcount⟩ := allocation_count_squared (Fintype.card α+2) (by omega) (δ/2) (half_pos hδ)
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C*Ccount,mul_pos hC hCcount,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth R G D hR hG hD H hH hcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B hB hprod hHR
  let ν := slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
  let Wslot := fun i=>slotProfile W (σ i) (freq i)
  let P := fun i=>Z^(w i)
  let f := fun (allocation : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)))(z : O)=>
    normalization (X₁*X₂) P*(frozenCoefficient B G R ν Wslot P*
      allocatedLiveSum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB G R D allocation ν Wslot P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
  let A := (C*(D.absNorm:ℝ)^(δ/2)/(G.absNorm:ℝ)/pairNorm d)*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+ε)
  let E := A*(Z^(κ*(∑i : liveIndices B,w i.val))/(D.absNorm:ℝ))
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hDpos : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hA : 0≤A := by
    have := diagonalControl_nonneg s.radial.profile
    have := pairNorm_pos hd.1 hd.2
    dsimp only [A]
    positivity
  have hE : 0≤E := mul_nonneg hA (div_nonneg (Real.rpow_nonneg hZ0.le _) hDpos.le)
  have hf (allocation : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2))) :
      radialEnergy (f allocation) (effectiveState s).radial.keep s.radial.profile s.radial.scale≤E := by
    have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
      R G D hR hG hD.ne_zero H hH hcap W₁ W₂ hs₁ hs₂
      t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B hB hprod hHR D (dvd_refl D) allocation
    have hcost := selected_budget_bound D hD allocation Z κ (fun i : liveIndices B=>w i.val)
      hZ.1.le (by linarith) (fun i=>hw i.val)
    apply he.trans
    apply (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left hcost hA)
    rw [show s.width+κ*(∑i : MixedLiteralAllocation.selectedLive D allocation,w i.val.val)+ε=
        s.width+ε+κ*(∑i : MixedLiteralAllocation.selectedLive D allocation,w i.val.val) by ring,
      Real.rpow_add hZ0]
    dsimp only [A]
    ring
  have hs := radial_phase_sum (fun (_ : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2))) (_ : O)=>(1:ℂ))
    f E (effectiveState s).radial.keep s.radial.profile s.radial.scale radial
    s.radial.scale_pos s.radial_support s.radial.nonneg (by intros;simp) hf
  simp only [one_mul] at hs
  have hrow (z : O) := masked_live_sum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
    (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB G R D hD ν Wslot P
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
  change radialEnergy (fun z=>normalization (X₁*X₂) P*(frozenCoefficient B G R ν Wslot P*
    maskedLiveSum (naturalCharacter s.character z) (enclosure (Cap*Z^Lcap)) H
      (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB G R D ν Wslot P
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂))
    (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤ _
  conv_lhs =>
    arg 1
    ext z
    rw [hrow z,Finset.mul_sum,Finset.mul_sum]
  apply hs.trans
  have hdim : Fintype.card (liveIndices B⊕Fin 2)≤Fintype.card α+2 := by
    simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_coe]
    exact Nat.add_le_add_right (Finset.card_le_univ _) 2
  apply (mul_le_mul_of_nonneg_right (hcount hdim D hD.ne_zero) hE).trans_eq
  have hpow : (D.absNorm:ℝ)^(δ/2)*(D.absNorm:ℝ)^(δ/2)=(D.absNorm:ℝ)^δ := by
    rw [←Real.rpow_add hDpos]
    congr 1
    ring
  rw [show s.width+κ*(∑i : liveIndices B,w i.val)+ε=
      s.width+ε+κ*(∑i : liveIndices B,w i.val) by ring,Real.rpow_add hZ0]
  dsimp only [E,A]
  calc
    _ = (C*Ccount)*((D.absNorm:ℝ)^(δ/2)*(D.absNorm:ℝ)^(δ/2))/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ)*
        diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
        (1+|t|+V)^degree*(Z^(s.width+ε)*Z^(κ*(∑i : liveIndices B,w i.val))) := by ring
    _ = _ := by rw [hpow]

end
end Candidate.FourthPower.MixedCommonMasked
