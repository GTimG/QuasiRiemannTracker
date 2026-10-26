import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.RestrictedIncumbent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false

/-! A LOW child of the first step deletes a slot length fixed by its parent's cell, not the length that restores the
old capacity. The deleted slots are paid on the LOW rows at the slot price `q` each; the remaining state keeps all its
rows, and its energy is bounded by the second step. -/

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional QuadraticInitialBound

variable {α : Type*}

/-- Whole slots of total length at least `d`, or all of them, and at most `d` plus one mesh step. -/
theorem fixed_slot_selection (J : Finset α) (w : α → ℝ) (d mesh : ℝ) (hd : 0 ≤ d) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh) :
    ∃ R : Finset α, R ⊆ J ∧ (∑ i ∈ R, w i) ≤ d + mesh ∧ (R = J ∨ d ≤ ∑ i ∈ R, w i) := by
  obtain ⟨R, hR, hbound, hcover, -⟩ :=
    whole_removal J w d (1/6) mesh hd (by norm_num) hm hw hwm
  refine ⟨R, hR, ?_, ?_⟩
  · have h := hbound.trans (min_le_right _ _)
    norm_num at h
    exact h
  · rcases hcover with h | h
    · exact Or.inl h
    · right
      norm_num at h
      exact h

/-- The energy of a natural state is nonnegative: its radial profile is. -/
theorem natural_energy_nonneg {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) :
    0 ≤ energy s.character s.mask 1 t W₁ W₂ S β P X₁ X₂ keep s.radial.profile s.radial.scale := by
  unfold energy
  refine tsum_nonneg (fun z => ?_)
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (s.radial.nonneg z)
  · exact le_rfl

/-- The LOW rows of a state, after deleting slots of total length at least `d` (or all its slots), cost the deleted
slots at the price `q` and the energy of the remaining state on all its rows. -/
theorem fixed_low_energy {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (low : O → Prop)
    (J : Finset α) (W₁ W₂ : ℝ → ℂ) (slots : α → Finset (Ideal O)) (coeff : α → Ideal O → ℂ)
    (t X₁ X₂ q d mesh : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hq : 0 ≤ q) (hd : 0 ≤ d) (hm : 0 ≤ mesh)
    (w B : α → ℝ) (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh) (hB : ∀ i ∈ J, 0 ≤ B i)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ J,
      ‖normalizedSlot s.character s.mask 1 z (slots i) (coeff i) t (Z ^ w i)‖ ^ 2 ≤ B i * Z ^ (q * w i)) :
    ∃ R : Finset α, R ⊆ J ∧ (∑ i ∈ R, w i) ≤ d + mesh ∧ (R = J ∨ d ≤ ∑ i ∈ R, w i) ∧
      energy s.character s.mask 1 t W₁ W₂ (fun i : J => slots i) (fun i : J => coeff i)
        (fun i : J => Z ^ w i) X₁ X₂ (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
      ((∏ i ∈ R, B i) * Z ^ (q * (d + mesh))) *
        energy s.character s.mask 1 t W₁ W₂ (fun i : ↥(J \ R) => slots i) (fun i : ↥(J \ R) => coeff i)
          (fun i : ↥(J \ R) => Z ^ w i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  have hZ : 1 ≤ Z := s.base_ge_one
  obtain ⟨R, hR, hsum, hcover⟩ := fixed_slot_selection J w d mesh hd hm hw hwm
  refine ⟨R, hR, hsum, hcover, ?_⟩
  have he := LocalMoment.restricted_energy_remove s low J R hR W₁ W₂ slots coeff (fun i => Z ^ w i) t X₁ X₂ q
    hX₁ hX₂ (fun i => Real.rpow_nonneg (zero_le_one.trans hZ) _) w B (fun i hi => hB i (hR hi))
    (fun z hk hl i hi => hslot z hk hl i (hR hi))
  refine he.trans (mul_le_mul_of_nonneg_right ?_ (natural_energy_nonneg s _ _ _ _ _ _ _ _ _))
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i hi => hB i (hR hi)))
  exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_left hsum hq)


variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A LOW child whose capacity holds once a slot length `d` is deleted is bounded by the old moment: the deleted
slots are paid at the price `q` on the LOW rows, and the remaining state is in the old region or has no slots. -/
theorem fixed_low_incumbent [Fintype α]
    (W : ℝ → ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C₀ C₁ : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzero : ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive : PositiveAt (α := α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C₁)
    (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwL : ∀ i, w i ≤ Lslot) (hσlo : ∀ i, lo ≤ σ i) (hσhi : ∀ i, σ i ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀ i, |v i| ≤ height)
    (s : NaturalState Z Bmask bΦ) (hQ : s.fixedModulus = internalQ Q η₀) (hs : s.width ≤ Mcap)
    (low : O → Prop) (p : Profiles a b) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hc₁ : X₁ ≤ Z ^ L) (hc₂ : X₂ ≤ Z ^ L) (hκ : 0 ≤ κ) (q d mesh : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) (hm : 0 ≤ mesh)
    (hwm : ∀ i ∈ J, w i ≤ mesh) (B : α → ℝ) (hB : ∀ i ∈ J, 0 ≤ B i)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ J,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H bslot (Z ^ w i))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ w i) (σ i) (v i) I) t (Z ^ w i)‖ ^ 2 ≤ B i * Z ^ (q * w i))
    (hO : length Z X₁ + length Z X₂ + 6*κ*((∑ i ∈ J, w i) - d) ≤ s.width) :
    ∃ R : Finset α, R ⊆ J ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : J => primePool M H bslot (Z ^ w i))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ w i) (σ i) (v i) I)
        (fun i : J => Z ^ w i) X₁ X₂ (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
      ((∏ i ∈ R, B i) * Z ^ (q * (d + mesh))) *
        ((C₀ + C₁) * diagonalControl s.radial.profile * (p.control S) ^ 2 * (1 + |t| + height) ^ degree *
          Z ^ (s.width + ε)) := by
  obtain ⟨R, hR, hsum, hcover, he⟩ := fixed_low_energy s low J (p.profile 0) (p.profile 1)
    (fun i => primePool M H bslot (Z ^ w i))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z ^ w i) (σ i) (v i) I)
    t X₁ X₂ q d mesh hX₁ hX₂ hq hd hm w B (fun i _ => hw i) hwm hB hslot
  refine ⟨R, hR, he.trans (mul_le_mul_of_nonneg_left ?_ ?_)⟩
  · apply remaining_energy_bound M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C₀ C₁
      hC₀ hC₁ hzero hpositive J R θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
    rcases hcover with hRJ | hdR
    · exact Or.inl hRJ
    · right
      have hsplit := Finset.sum_sdiff hR (f := w)
      nlinarith
  · exact mul_nonneg (Finset.prod_nonneg (fun i hi => hB i (hR hi)))
      (Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _)
end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
