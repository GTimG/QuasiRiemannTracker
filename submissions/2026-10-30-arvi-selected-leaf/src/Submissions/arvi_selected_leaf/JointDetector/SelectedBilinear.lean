/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.SelectedKernel
import Submissions.arvi_selected_leaf.JointDetector.IdealCoprimeMass

/-!
# Selected bilinear reflection bounds after divisor expansion

The two dual row vectors are independent. The first whole polynomial is
conjugated before using the selected operator norm. Divisor selectors are
expanded outside the source sum and paid by their row incidence.
No entrywise monotonicity of a signed coprimality mask is used.
-/

namespace Qrh.JointDetector

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI
local notation "O" => ActualEisensteinCubic.O

theorem selectedNorm_nonneg (rows : Finset O) (sources : Finset (Ideal O)) :
    0 ≤ selectedNorm rows sources := sq_nonneg _

/-- The source weight is common, and neither dual vector need be a conjugate
of the other. Every source ideal and every natural matrix zero is retained. -/
def selectedBilinear (rows : Finset O) (sources : Finset (Ideal O))
    (A B : rows → ℂ) (w : sources → ℂ) : ℂ :=
  ∑ I : sources, w I *
    (∑ r : rows, A r * star (selectedMatrix rows sources I r)) *
    (∑ r : rows, B r * selectedMatrix rows sources I r)

/-- Finite weighted bilinear Cauchy for the exact selected operator norm. -/
theorem selectedBilinear_le (rows : Finset O) (sources : Finset (Ideal O))
    (A B : rows → ℂ) (w : sources → ℂ) (hw : ∀ I, ‖w I‖ ≤ 1) :
    ‖selectedBilinear rows sources A B w‖ ≤
      selectedNorm rows sources * Real.sqrt (∑ r, ‖A r‖ ^ 2) *
        Real.sqrt (∑ r, ‖B r‖ ^ 2) := by
  let L : sources → ℂ := fun I =>
    ∑ r : rows, A r * star (selectedMatrix rows sources I r)
  let R : sources → ℂ := fun I =>
    ∑ r : rows, B r * selectedMatrix rows sources I r
  have hleft (I : sources) :
      ‖L I‖ = ‖∑ r : rows, selectedMatrix rows sources I r * star (A r)‖ := by
    have heq : L I = star (∑ r : rows, selectedMatrix rows sources I r * star (A r)) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [star_mul, star_star]
    rw [heq, norm_star]
  have hright (I : sources) :
      R I = ∑ r : rows, selectedMatrix rows sources I r * B r := by
    apply Finset.sum_congr rfl
    intro r _
    exact mul_comm _ _
  have hEL : (∑ I : sources, ‖L I‖ ^ 2) ≤
      selectedNorm rows sources * ∑ r : rows, ‖A r‖ ^ 2 := by
    simp_rw [hleft]
    simpa only [selectedDualEnergy, norm_star] using
      selectedDualEnergy_le rows sources (fun r => star (A r))
  have hER : (∑ I : sources, ‖R I‖ ^ 2) ≤
      selectedNorm rows sources * ∑ r : rows, ‖B r‖ ^ 2 := by
    simp_rw [hright]
    exact selectedDualEnergy_le rows sources B
  have hK := selectedNorm_nonneg rows sources
  calc
    ‖selectedBilinear rows sources A B w‖ ≤ ∑ I : sources, ‖w I * L I * R I‖ :=
      norm_sum_le _ _
    _ ≤ ∑ I : sources, ‖L I‖ * ‖R I‖ := by
      apply Finset.sum_le_sum
      intro I _
      simp only [norm_mul]
      have hweight := mul_le_mul_of_nonneg_right (hw I)
        (mul_nonneg (norm_nonneg (L I)) (norm_nonneg (R I)))
      nlinarith
    _ ≤ Real.sqrt (∑ I : sources, ‖L I‖ ^ 2) *
        Real.sqrt (∑ I : sources, ‖R I‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ (fun I => ‖L I‖) (fun I => ‖R I‖)
    _ ≤ Real.sqrt (selectedNorm rows sources * ∑ r : rows, ‖A r‖ ^ 2) *
        Real.sqrt (selectedNorm rows sources * ∑ r : rows, ‖B r‖ ^ 2) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hEL) (Real.sqrt_le_sqrt hER)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hK, Real.sqrt_mul hK]
      rw [show Real.sqrt (selectedNorm rows sources) *
          Real.sqrt (∑ r : rows, ‖A r‖ ^ 2) *
          (Real.sqrt (selectedNorm rows sources) * Real.sqrt (∑ r : rows, ‖B r‖ ^ 2)) =
          (Real.sqrt (selectedNorm rows sources))^2 *
            Real.sqrt (∑ r : rows, ‖A r‖ ^ 2) * Real.sqrt (∑ r : rows, ‖B r‖ ^ 2) by ring]
      rw [Real.sq_sqrt hK]

/-- A mask restricts the coefficient vector; the source matrix is unchanged. -/
def maskedRowVector {E R : Type*} (mask : E → R → Prop)
    [∀ e r, Decidable (mask e r)] (A : R → ℂ) (e : E) (r : R) : ℂ :=
  if mask e r then A r else 0

theorem maskedRowVector_energy {E R : Type*} [Fintype R]
    (mask : E → R → Prop) [∀ e r, Decidable (mask e r)] (A : R → ℂ) (e : E) :
    (∑ r, ‖maskedRowVector mask A e r‖ ^ 2) = maskedEnergy mask A e := by
  simp only [maskedRowVector, maskedEnergy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp

/-- A single expanded selector, including its complex Möbius phase. -/
theorem masked_selectedBilinear_le {E : Type*}
    (rows : Finset O) (sources : Finset (Ideal O))
    (mask : E → rows → Prop) [∀ e r, Decidable (mask e r)]
    (A B : rows → ℂ) (w : sources → ℂ) (μ : E → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (hμ : ∀ e, ‖μ e‖ ≤ 1) (e : E) :
    ‖μ e * selectedBilinear rows sources
        (maskedRowVector mask A e) (maskedRowVector mask B e) w‖ ≤
      selectedNorm rows sources * Real.sqrt (maskedEnergy mask A e) *
        Real.sqrt (maskedEnergy mask B e) := by
  calc
    _ ≤ ‖selectedBilinear rows sources (maskedRowVector mask A e)
        (maskedRowVector mask B e) w‖ := by
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hμ e) (norm_nonneg _)
    _ ≤ _ := by
      simpa only [maskedRowVector_energy] using selectedBilinear_le rows sources
        (maskedRowVector mask A e) (maskedRowVector mask B e) w hw

/-- After expanding the pair selector, Cauchy costs only row incidence.
The arbitrary label phases and the independent dual vectors are preserved. -/
theorem selectedBilinear_masks_le {E : Type*} [Fintype E]
    (rows : Finset O) (sources : Finset (Ideal O))
    (mask : E → rows → Prop) [∀ e r, Decidable (mask e r)]
    (A B : rows → ℂ) (w : sources → ℂ) (μ : E → ℂ)
    (D : ℝ) (hD : 0 ≤ D)
    (hincidence : ∀ r, ((Finset.univ.filter fun e => mask e r).card : ℝ) ≤ D)
    (hw : ∀ I, ‖w I‖ ≤ 1) (hμ : ∀ e, ‖μ e‖ ≤ 1) :
    ‖∑ e, μ e * selectedBilinear rows sources
        (maskedRowVector mask A e) (maskedRowVector mask B e) w‖ ≤
      selectedNorm rows sources * D * Real.sqrt (∑ r, ‖A r‖ ^ 2) *
        Real.sqrt (∑ r, ‖B r‖ ^ 2) := by
  exact coprime_mask_bilinear_sum_le mask A B _ D (selectedNorm rows sources)
    hD (selectedNorm_nonneg rows sources) hincidence
    (masked_selectedBilinear_le rows sources mask A B w μ hw hμ)

/-- Actual ideal-divisor selectors, with their full `Cε B^ε` cost. -/
theorem selectedBilinear_idealDivisors_le
    (rows : Finset O) (sources labels : Finset (Ideal O)) (row : rows → Ideal O)
    (A B : rows → ℂ) (w : sources → ℂ) (μ : labels → ℂ)
    (Bnorm ε : ℝ) (hB : 0 ≤ Bnorm) (hε : 0 < ε)
    (hnonzero : ∀ r, row r ≠ ⊥)
    (hnorm : ∀ r, (Ideal.absNorm (row r) : ℝ) ≤ Bnorm)
    (hw : ∀ I, ‖w I‖ ≤ 1) (hμ : ∀ e, ‖μ e‖ ≤ 1) :
    ‖∑ e : labels, μ e * selectedBilinear rows sources
        (maskedRowVector (idealDivisorMask labels row) A e)
        (maskedRowVector (idealDivisorMask labels row) B e) w‖ ≤
      selectedNorm rows sources * (idealDivisorConstant ε hε * Bnorm ^ ε) *
        Real.sqrt (∑ r, ‖A r‖ ^ 2) * Real.sqrt (∑ r, ‖B r‖ ^ 2) := by
  exact selectedBilinear_masks_le rows sources (idealDivisorMask labels row)
    A B w μ (idealDivisorConstant ε hε * Bnorm ^ ε)
    (mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg hB ε))
    (fun r => idealDivisorMask_incidence_small_power labels row r (hnonzero r)
      ε hε Bnorm (hnorm r)) hw hμ

/-- Principal ideals of the actual natural row elements give the literal mask
`e ∣ (row)` used by the pair-Poisson divisor expansion. -/
theorem selectedBilinear_naturalRowDivisors_le
    (rows : Finset O) (sources labels : Finset (Ideal O))
    (A B : rows → ℂ) (w : sources → ℂ) (μ : labels → ℂ)
    (Bnorm ε : ℝ) (hB : 0 ≤ Bnorm) (hε : 0 < ε)
    (hnonzero : ∀ r : rows, r.val ≠ 0)
    (hnorm : ∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ≤ Bnorm)
    (hw : ∀ I, ‖w I‖ ≤ 1) (hμ : ∀ e, ‖μ e‖ ≤ 1) :
    ‖∑ e : labels, μ e * selectedBilinear rows sources
        (maskedRowVector (idealDivisorMask labels (fun r : rows => Ideal.span {r.val})) A e)
        (maskedRowVector (idealDivisorMask labels (fun r : rows => Ideal.span {r.val})) B e) w‖ ≤
      selectedNorm rows sources * (idealDivisorConstant ε hε * Bnorm ^ ε) *
        Real.sqrt (∑ r, ‖A r‖ ^ 2) * Real.sqrt (∑ r, ‖B r‖ ^ 2) := by
  exact selectedBilinear_idealDivisors_le rows sources labels
    (fun r : rows => Ideal.span {r.val}) A B w μ Bnorm ε hB hε
    (fun r => by
      intro hz
      apply hnonzero r
      have hm : r.val ∈ (Ideal.span {r.val} : Ideal O) := Ideal.subset_span (by simp)
      rw [hz] at hm
      simpa only [Ideal.mem_bot] using hm)
    hnorm hw hμ

end

end Qrh.JointDetector
