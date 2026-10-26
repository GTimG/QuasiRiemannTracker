import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PaidBands

/-! Low-bin source payment: remove slots only on the restricted rows,
then apply the incumbent moment to the remaining exact natural state. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.LocalMoment
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidBands CenteredMomentEnergyCapacityRemoval
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentHeckeSlots
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound
open CenteredMomentRetainedEnergy
local notation "O" => HeckeFamily.O

variable {α : Type*}

/-- Post-transform row restriction is kept while paying removed slots.
The remaining nonnegative norm is enlarged only after this payment. -/
theorem restricted_energy_remove {Z Bmask bΦ : ℝ}
    (s : NaturalState Z Bmask bΦ) (low : O → Prop)
    (J R : Finset α) (hR : R ⊆ J)
    (W₁ W₂ : ℝ → ℂ) (slots : α → Finset (Ideal O))
    (coeff : α → Ideal O → ℂ) (P : α → ℝ)
    (t X₁ X₂ κlow : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hP : ∀ i, 0 ≤ P i) (w B : α → ℝ) (hB : ∀ i ∈ R, 0 ≤ B i)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ R,
      ‖normalizedSlot s.character s.mask 1 z (slots i) (coeff i) t (P i)‖ ^ 2 ≤
        B i * Z ^ (κlow * w i)) :
    energy s.character s.mask 1 t W₁ W₂ (fun i : J => slots i)
      (fun i : J => coeff i) (fun i : J => P i) X₁ X₂
      (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
      ((∏ i ∈ R, B i) * Z ^ (κlow * ∑ i ∈ R, w i)) *
        energy s.character s.mask 1 t W₁ W₂ (fun i : ↥(J \ R) => slots i)
          (fun i : ↥(J \ R) => coeff i) (fun i : ↥(J \ R) => P i) X₁ X₂
          s.radial.keep s.radial.profile s.radial.scale := by
  classical
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  let cost := (∏ i ∈ R, B i) * Z ^ (κlow * ∑ i ∈ R, w i)
  have hcost : 0 ≤ cost := mul_nonneg (Finset.prod_nonneg hB) (Real.rpow_nonneg hZ.le _)
  have hsum (T : Finset α) (keep : O → Prop) := compact_radial_summable
    (fun z => positiveSlotRow s.character s.mask 1 z W₁ W₂
      (fun i : T => slots i) (fun i : T => coeff i) (fun i : T => P i) t X₁ X₂)
    keep s.radial.profile s.radial.scale bΦ s.radial.scale_pos s.radial_support
  unfold energy
  rw [← tsum_mul_left]
  apply (hsum J (fun z => s.radial.keep z ∧ low z)).tsum_le_tsum _
    ((hsum (J \ R) s.radial.keep).mul_left cost)
  intro z
  by_cases hk : s.radial.keep z
  · by_cases hl : low z
    · simp only [hk, hl, and_self, ite_true]
      have hh := selectedProduct_energy_remove J R hR s.character s.mask 1 z W₁ W₂
        slots coeff P t X₁ X₂ Z κlow hZ w B hB (hslot z hk hl)
      rw [selected_eq_positive J s.character s.mask 1 z W₁ W₂ slots coeff P t X₁ X₂
        (mul_pos hX₁ hX₂).le hP,
        selected_eq_positive (J \ R) s.character s.mask 1 z W₁ W₂ slots coeff P
          t X₁ X₂ (mul_pos hX₁ hX₂).le hP] at hh
      exact (mul_le_mul_of_nonneg_right hh (s.radial.nonneg z)).trans_eq (by ring)
    · simp only [hk, hl, and_false, ite_false, ite_true]
      exact mul_nonneg hcost (mul_nonneg (sq_nonneg _) (s.radial.nonneg z))
  · simp only [hk, false_and, ite_false, mul_zero, le_refl]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The low-bin removal rate and the incumbent capacity rate are separate.
This theorem calls only the incumbent positive or zero-slot moment on the
remaining state, including every original mask and eligibility predicate. -/
theorem restricted_paid_incumbent
    (W : ℝ → ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κbase Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C₀ C₁ : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzero : ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive : PositiveAt (α := α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κbase Z η₀ Q degree S C₁)
    (J R : Finset α) (hR : R ⊆ J) (θ : α → RayQuotient.Characters M H)
    (w σ v : α → ℝ) (t height κlow : ℝ) (B : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwL : ∀ i, w i ≤ Lslot)
    (hσlo : ∀ i, lo ≤ σ i) (hσhi : ∀ i, σ i ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀ i, |v i| ≤ height) (hB : ∀ i ∈ R, 0 ≤ B i)
    (s : NaturalState Z Bmask bΦ) (hQ : s.fixedModulus = internalQ Q η₀)
    (hs : s.width ≤ Mcap) (low : O → Prop) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hc₁ : X₁ ≤ Z ^ L) (hc₂ : X₂ ≤ Z ^ L)
    (hcapacity : R = J ∨
      length Z X₁ + length Z X₂ + 6 * κbase * (∑ i ∈ J \ R, w i) ≤ s.width)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ R,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H bslot (Z ^ (w i)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
        t (Z ^ (w i))‖ ^ 2 ≤ B i * Z ^ (κlow * w i)) :
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : J => primePool M H bslot (Z ^ (w i)))
      (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
      (fun i : J => Z ^ (w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
      s.radial.profile s.radial.scale ≤
      (∏ i ∈ R, B i) * ((C₀ + C₁) * diagonalControl s.radial.profile *
        (p.control S) ^ 2 * (1 + |t| + height) ^ degree) *
        Z ^ (s.width + ε + κlow * ∑ i ∈ R, w i) := by
  classical
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  have he := restricted_energy_remove s low J R hR (p.profile 0) (p.profile 1)
    (fun i => primePool M H bslot (Z ^ (w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
    (fun i => Z ^ (w i)) t X₁ X₂ κlow hX₁ hX₂
    (fun i => Real.rpow_nonneg hZ.le _) w B hB hslot
  have hb := remaining_energy_bound M H hH W bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κbase Z η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpositive
    J R θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hc₁ hc₂ hcapacity
  apply he.trans ((mul_le_mul_of_nonneg_left hb
    (mul_nonneg (Finset.prod_nonneg hB) (Real.rpow_nonneg hZ.le _))).trans_eq ?_)
  simp only [Real.rpow_add hZ]
  ring

end SevenEighths.LocalMoment
end
end OAI
