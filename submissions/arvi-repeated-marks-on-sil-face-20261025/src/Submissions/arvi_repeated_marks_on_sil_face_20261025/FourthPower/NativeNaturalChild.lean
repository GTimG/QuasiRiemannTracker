/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Apply the proved nonfixed estimate to literal natural-character children.
Ordinary lengths are divided by their actual ideal norms, and all inherited
heights are retained. Common punctures remain in the parent state.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.NativeNonfixedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChild

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Candidate.FourthPower.NativeNaturalChild
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem shortened_children {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (aslot bslot a b radial Mcap L Lslot ε lo hi κ : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hrad : 0<radial) (hM : 0<Mcap) (hLslot : 0≤Lslot) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤V → (∀i∈F,|freq i|≤V) →
    ∀Bmask : ℝ,∀s : NaturalState Z Bmask radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀A : Finset α,A⊆F → ∀W₁ W₂ : 𝓢(ℝ,ℂ),
    ∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
        polynomial (naturalCharacter s.character z) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
        ∏i∈A,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i∈F,w i)+ε) := by
  obtain ⟨degree,S,hbound⟩ := NativeNonfixedEnergy.canonical_energy M H hH F W
    aslot bslot a b radial Mcap L Lslot ε lo hi κ haslot hWs hW ha haUpper hb hrad hM
    hLslot hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbound⟩ := hbound η₀ hQη
  refine ⟨C,hC,hbound.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V hw hwL hσ hσhi hV hfreq Bmask s hQ hwidth A hAF
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂
  have hn (D : Ideal O) (hD : D≠0) : (1:ℝ)≤D.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hd₁ : 0<(D₁.absNorm:ℝ) := zero_lt_one.trans_le (hn D₁ hD₁)
  have hd₂ : 0<(D₂.absNorm:ℝ) := zero_lt_one.trans_le (hn D₂ hD₂)
  have he := hZ.2 θ w σ (fun i=>t+freq i) 0 (|t|+V) hw hwL hσ hσhi
    (add_nonneg (abs_nonneg t) hV)
    (fun i hi=>(abs_add_le t (freq i)).trans (add_le_add le_rfl (hfreq i hi)))
    (unpuncturedState s) rfl hQ hwidth A hAF
    (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂)
    (X₁/(D₁.absNorm:ℝ)) (X₂/(D₂.absNorm:ℝ)) (div_pos hX₁ hd₁) (div_pos hX₂ hd₂)
    ((div_le_self hX₁.le (hn D₁ hD₁)).trans hc₁)
    ((div_le_self hX₂.le (hn D₂ hD₂)).trans hc₂)
  rw [independent_child_ray_energy s ha W₁ W₂ hs₁ hs₂ A
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>relativeCharacter M H hH η₀ (θ i)) (fun _=>W) (fun i=>Z^(w i)) σ freq
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
    t t₁ t₂ _ _ (div_pos hX₁ hd₁) (div_pos hX₂ hd₂)]
  simpa only [unpuncturedState,NaturalState.width,NaturalState.mask,effectiveState,effectiveRadial,
    abs_zero,add_zero,add_assoc] using he

end
end Candidate.FourthPower.NativeNaturalChild
