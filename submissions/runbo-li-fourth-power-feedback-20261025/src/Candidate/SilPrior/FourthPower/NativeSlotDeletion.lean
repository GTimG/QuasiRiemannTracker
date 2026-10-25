/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Canonical prime slots can be deleted inside the actual positive physical
energy. No estimate is asserted for arbitrary bounded slot coefficients.
The unpunctured state is the one produced after common-mask completion.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CapacityRemoval
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.SilPrior.FourthPower.NativeSlotDeletion
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyCapacityRemoval
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRayMaskedFloor CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

/-- An exact integration step: the same zero row, lengths and radial support
remain after paying a uniform bound for the product of normalized slots. -/
theorem energy_delete {α : Type*} [DecidableEq α]
    {Z Bmask radial : ℝ} (s : NaturalState Z Bmask radial) (hu : s.puncture=1)
    (F : Finset α) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0≤P i) (W₁ W₂ : ℝ→ℂ) (t X₁ X₂ E : ℝ)
    (hX : 0≤X₁*X₂)
    (hslot : ∀z,s.radial.keep z →
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)≠0 →
      ‖∏i∈F,normalizedSlot s.character fixedBadMask 1 z (pool i) (β i) t (P i)‖^2≤E) :
    energy s.character s.mask 1 t W₁ W₂
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale ≤
      E*zeroEnergy s.character s.mask 1 t W₁ W₂ X₁ X₂ s.radial := by
  have hm : s.mask=fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1 := by
    rw [NaturalState.mask,hu]
  rw [hm,zero_energy_eq,unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero,
    unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero,←zero_energy_eq]
  have hs := compact_radial_summable
    (fun z=>positiveSlotRow s.character fixedBadMask 1 z W₁ W₂
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) t X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale radial s.radial.scale_pos s.radial_support
  have hz := compact_radial_summable
    (fun z=>zeroRow s.character fixedBadMask 1 z t W₁ W₂ X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale radial s.radial.scale_pos s.radial_support
  unfold energy zeroEnergy
  rw [←tsum_mul_left]
  apply hs.tsum_le_tsum _ (hz.mul_left E)
  intro z
  by_cases hk : s.radial.keep z
  · simp only [ite_eq_left hk]
    by_cases hp : s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)=0
    · simp [hp]
    · rw [←selected_eq_positive F _ _ _ _ _ _ _ _ _ _ _ _ hX hP]
      change ‖zeroRow s.character fixedBadMask 1 z t W₁ W₂ X₁ X₂ *
        ∏i∈F,normalizedSlot s.character fixedBadMask 1 z (pool i) (β i) t (P i)‖^2 * _ ≤ _
      rw [norm_mul,mul_pow]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hslot z hk hp) (sq_nonneg _))
        (s.radial.nonneg z)).trans_eq (by ring)
  · simp only [ite_eq_right hk,mul_zero,le_refl]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Canonical annular slots, with all original frequencies and ray factors.
Constants precede the moving state, subset, profiles and positive lengths. -/
theorem canonical_delete {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b radial Mcap Lslot loss lo hi κ : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hrad : 0≤radial) (hM : 0≤Mcap) (hL : 0≤Lslot) (hloss : 0<loss)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤V → (∀i∈F,|freq i|≤V) →
    ∀Bmask : ℝ,∀s : NaturalState Z Bmask radial,s.puncture=1 → s.width≤Mcap →
    ∀Q : Ideal O,s.fixedModulus=internalQ Q η₀ → Q≤M →
    ∀(A : Finset α),A⊆F → ∀(W₁ W₂ : ℝ→ℂ)(X₁ X₂ : ℝ),0<X₁ → 0<X₂ →
      energy s.character s.mask 1 t W₁ W₂
        (fun i:A=>primePool M H b (Z^(w i)))
        (fun (i:A) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:A=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (C*(1+|t|+V)^degree*Z^(loss+κ*(∑i∈F,w i)))*
        zeroEnergy s.character s.mask 1 t W₁ W₂ X₁ X₂ s.radial := by
  obtain ⟨degree,C,hC,hslots⟩ := natural_slot_product M H hH F W a b ha hWs hW
    (Mcap+1) Lslot loss lo hi κ (by linarith) hL hloss hβ hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [hslots η₀,eventual_state_conductor radial Mcap hrad] with Z hs hc
  refine ⟨hc.1,?_⟩
  intro θ w σ freq t V hw hwL hσ hσhi hV hfreq Bmask s hu hwidth Q hQ hQM A hAF
    W₁ W₂ X₁ X₂ hX₁ hX₂
  apply energy_delete s hu A (fun i=>primePool M H b (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) (fun _=>Real.rpow_nonneg (zero_lt_one.trans hc.1).le _)
    W₁ W₂ t X₁ X₂ _ (mul_pos hX₁ hX₂).le
  intro z hk hp
  have hn := s.row_ne_zero z hk
  have hh := hs θ w σ freq t V hw hwL hσ hσhi hV hfreq s.character z hn
    (naturalRow s.character z hn) (hc.2 Bmask s hwidth z hn hp) Q hQM
    (state_unit_nonexceptional s hu _ hQ z hk) A hAF
  simpa only [natural_slot_eq (naturalRow s.character z hn)] using hh

end
end Candidate.SilPrior.FourthPower.NativeSlotDeletion
