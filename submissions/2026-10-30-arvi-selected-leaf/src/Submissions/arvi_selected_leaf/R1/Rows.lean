/-
The packed rows as polynomials of the radical row character, slot peeling, and the swap of the plain sums.

* `psr_norm_eq`: at a nonzero row, `|positiveSlotRow| = |poly(χ_z, W₁, X₁) · poly(χ_z, W₂, X₂) · ∏ slots|` with
  `χ_z = radRow η m z` (the factors `X^{it}` are unimodular), hence the energy is a radial energy of polynomial
  products (`energy_eq_radial`).
* `slot_norm_sq_le`: a normalized slot over `N` sources with coefficients `≤ B` has square at most `N² B² / P`.
* `exists_sub_weight`: a sub-block of total weight in `[S - mesh, S]`.
* `energy_swap`: the energy is symmetric in the two plain sums.
-/
import Submissions.arvi_selected_leaf.R1.ReflectedClass

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths CanonicalRowCompletion HeckeFamily HeckeRowClosure HeckeDyadic ConcreteTraceCRT
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentOriginalRadialComparison
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

variable {ι : Type*} [Fintype ι]

/-- **The packed row is a product of polynomials of the radical row character**, up to unimodular factors. -/
theorem psr_norm_eq (η : Character) (m z : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (hz : z ≠ 0) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) :
    ‖positiveSlotRow η m 1 z W₁ W₂ S β P t X₁ X₂‖ =
      ‖polynomial (radRow η m z hm hmLam hm2) false W₁ X₁ 0 t *
        polynomial (radRow η m z hm hmLam hm2) false W₂ X₂ 0 t *
        ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i)‖ := by
  have hrow : ∀ n, elementCoeff (radRow η m z hm hmLam hm2) n = rowTwist (elementHom η) m 1 (1*z) n := by
    intro n
    rw [one_mul]
    exact (radRow_spec η m z hm hmLam hm2 hz).2 n
  have e₁ := plain_eq_polynomial η (radRow η m z hm hmLam hm2) m 1 z hrow W₁ t X₁ hX₁
  have e₂ := plain_eq_polynomial η (radRow η m z hm hmLam hm2) m 1 z hrow W₂ t X₂ hX₂
  have hsplit : positiveSlotRow η m 1 z W₁ W₂ S β P t X₁ X₂ =
      ((Real.sqrt X₁ : ℂ)⁻¹ * rowTwistedSum η m 1 z W₁ t X₁) *
        ((Real.sqrt X₂ : ℂ)⁻¹ * rowTwistedSum η m 1 z W₂ t X₂) *
        ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i) := by
    unfold positiveSlotRow
    simp only [normalizedSlot]
    have hPpos : 0 ≤ ∏ i, P i := Finset.prod_nonneg (fun i _ => (hP i).le)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hX₁.le, Real.sqrt_prod _ (fun i _ => (hP i).le)]
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    ring
  rw [hsplit, e₁, e₂]
  simp only [norm_mul]
  rw [norm_height_factor X₁ t hX₁, norm_height_factor X₂ t hX₂]
  ring

/-- **The energy as a radial energy of polynomial products.** -/
theorem energy_eq_radial (η : Character) (m : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2:O) ∣ m)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i)
    (keep : O → Prop) (hnz : ∀ z, keep z → z ≠ 0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m 1 t W₁ W₂ S β P X₁ X₂ keep Φ K =
      radialEnergy (fun z => polynomial (radRow η m z hm hmLam hm2) false W₁ X₁ 0 t *
        polynomial (radRow η m z hm hmLam hm2) false W₂ X₂ 0 t *
        ∏ i, normalizedSlot η m 1 z (S i) (β i) t (P i)) keep Φ K := by
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  split_ifs with hk
  · rw [psr_norm_eq η m z hm hmLam hm2 (hnz z hk) W₁ W₂ S β P t X₁ X₂ hX₁ hX₂ hP]
  · rfl

/-- A normalized slot over at most `N` sources with coefficients at most `B`. -/
theorem slot_norm_sq_le (η : Character) (m A z : O) (pool : Finset (Ideal O)) (β : Ideal O → ℂ)
    (t P : ℝ) (hP : 0 < P) (Bβ N : ℝ) (hB : 0 ≤ Bβ) (hβ : ∀ I ∈ pool, ‖β I‖ ≤ Bβ)
    (hN : (pool.card : ℝ) ≤ N) :
    ‖normalizedSlot η m A z pool β t P‖^2 ≤ N^2 * Bβ^2 / P := by
  have h1 : ‖normalizedSlot η m A z pool β t P‖ ≤ (Real.sqrt P)⁻¹ * (N * Bβ) := by
    unfold normalizedSlot
    rw [norm_mul, rowSlot_eq_weight, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    calc ‖∑ I ∈ pool, β I * rowWeight η m A z t I‖
        ≤ ∑ I ∈ pool, ‖β I * rowWeight η m A z t I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ pool, Bβ := Finset.sum_le_sum (fun I hI => by
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _)
            (CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all η m A z t I)).trans (hβ I hI))
      _ = (pool.card : ℝ) * Bβ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * Bβ := mul_le_mul_of_nonneg_right hN hB
  have h0 : 0 ≤ ‖normalizedSlot η m A z pool β t P‖ := norm_nonneg _
  calc ‖normalizedSlot η m A z pool β t P‖^2 ≤ ((Real.sqrt P)⁻¹ * (N * Bβ))^2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = N^2 * Bβ^2 / P := by
        rw [mul_pow, inv_pow, Real.sq_sqrt hP.le]
        field_simp

/-- **A sub-block of prescribed weight**: if all weights are at most `mesh` and the total exceeds `S ≥ 0`,
some sub-block has weight in `[S - mesh, S]`. -/
theorem exists_sub_weight {α : Type*} [DecidableEq α] (w : α → ℝ) (mesh S : ℝ) (hS : 0 ≤ S)
    (hwm : ∀ i, w i ≤ mesh) (T : Finset α) (hT : S < ∑ i ∈ T, w i) :
    ∃ T' ⊆ T, S - mesh ≤ ∑ i ∈ T', w i ∧ ∑ i ∈ T', w i ≤ S := by
  induction T using Finset.induction_on with
  | empty => simp at hT; linarith
  | insert a T₀ ha ih =>
    rw [Finset.sum_insert ha] at hT
    by_cases h₀ : S < ∑ i ∈ T₀, w i
    · obtain ⟨T', hT', h1, h2⟩ := ih h₀
      exact ⟨T', hT'.trans (Finset.subset_insert a T₀), h1, h2⟩
    · rw [not_lt] at h₀
      refine ⟨T₀, Finset.subset_insert a T₀, ?_, h₀⟩
      linarith [hwm a]

/-- **The energy is symmetric in the two plain sums.** -/
theorem energy_swap (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K = energy η m A t W₂ W₁ S β P X₂ X₁ keep Φ K := by
  unfold energy positiveSlotRow
  apply tsum_congr
  intro z
  split_ifs
  · congr 3
    rw [show X₂ * X₁ * ∏ i, P i = X₁ * X₂ * ∏ i, P i by ring]
    ring
  · rfl

end
end QRH.ArviSelectedLeaf.R1
