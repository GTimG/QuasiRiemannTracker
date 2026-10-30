/- Copyright (c) 2026 Joseph Bebel. -/
import Mathlib

/-!
# Mass of finite row masks with bounded incidence

Summing the local Cauchy--Schwarz masses costs the maximum number of masks
containing a row. It does not cost the total number of mask labels.
-/

namespace Qrh.JointDetector
noncomputable section
open scoped BigOperators
set_option autoImplicit false

/-- Squared mass of a complex vector on one row mask. -/
def maskedEnergy {E R : Type*} [Fintype R] (mask : E → R → Prop)
    [∀ e r, Decidable (mask e r)] (a : R → ℂ) (e : E) : ℝ :=
  ∑ r ∈ Finset.univ.filter (mask e), ‖a r‖ ^ 2

theorem maskedEnergy_nonneg {E R : Type*} [Fintype R] (mask : E → R → Prop)
    [∀ e r, Decidable (mask e r)] (a : R → ℂ) (e : E) :
    0 ≤ maskedEnergy mask a e :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Exact double counting: every row's energy is charged its incidence count. -/
theorem sum_maskedEnergy_eq {E R : Type*} [Fintype E] [Fintype R]
    (mask : E → R → Prop) [∀ e r, Decidable (mask e r)] (a : R → ℂ) :
    ∑ e, maskedEnergy mask a e =
      ∑ r, ((Finset.univ.filter fun e => mask e r).card : ℝ) * ‖a r‖ ^ 2 := by
  simp only [maskedEnergy, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]

/-- Bounded row incidence controls the sum of all masked energies. -/
theorem sum_maskedEnergy_le {E R : Type*} [Fintype E] [Fintype R]
    (mask : E → R → Prop) [∀ e r, Decidable (mask e r)] (a : R → ℂ) (D : ℝ)
    (hincidence : ∀ r, ((Finset.univ.filter fun e => mask e r).card : ℝ) ≤ D) :
    ∑ e, maskedEnergy mask a e ≤ D * ∑ r, ‖a r‖ ^ 2 := by
  rw [sum_maskedEnergy_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (hincidence r) (sq_nonneg _)

/-- Divisor-selector Cauchy: the local two-vector masses cost only the
maximum incidence, uniformly in both arbitrary complex row vectors. -/
theorem coprime_mask_mass_le {E R : Type*} [Fintype E] [Fintype R]
    (mask : E → R → Prop) [∀ e r, Decidable (mask e r)]
    (a b : R → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hincidence : ∀ r, ((Finset.univ.filter fun e => mask e r).card : ℝ) ≤ D) :
    ∑ e, Real.sqrt (maskedEnergy mask a e) * Real.sqrt (maskedEnergy mask b e) ≤
      D * Real.sqrt (∑ r, ‖a r‖ ^ 2) * Real.sqrt (∑ r, ‖b r‖ ^ 2) := by
  calc
    _ ≤ Real.sqrt (∑ e, maskedEnergy mask a e) *
        Real.sqrt (∑ e, maskedEnergy mask b e) :=
      Real.sum_sqrt_mul_sqrt_le _ (maskedEnergy_nonneg mask a) (maskedEnergy_nonneg mask b)
    _ ≤ Real.sqrt (D * ∑ r, ‖a r‖ ^ 2) * Real.sqrt (D * ∑ r, ‖b r‖ ^ 2) := by
      exact mul_le_mul
        (Real.sqrt_le_sqrt (sum_maskedEnergy_le mask a D hincidence))
        (Real.sqrt_le_sqrt (sum_maskedEnergy_le mask b D hincidence))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (Real.sqrt D) ^ 2 * Real.sqrt (∑ r, ‖a r‖ ^ 2) *
        Real.sqrt (∑ r, ‖b r‖ ^ 2) := by
      rw [Real.sqrt_mul hD, Real.sqrt_mul hD]
      ring
    _ = _ := by rw [Real.sq_sqrt hD]

/-- A family of per-mask bilinear estimates can be summed with this same
incidence cost. The complex values may carry arbitrary signs and phases. -/
theorem coprime_mask_bilinear_sum_le {E R : Type*} [Fintype E] [Fintype R]
    (mask : E → R → Prop) [∀ e r, Decidable (mask e r)]
    (a b : R → ℂ) (v : E → ℂ) (D K : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hincidence : ∀ r, ((Finset.univ.filter fun e => mask e r).card : ℝ) ≤ D)
    (hlocal : ∀ e, ‖v e‖ ≤
      K * Real.sqrt (maskedEnergy mask a e) * Real.sqrt (maskedEnergy mask b e)) :
    ‖∑ e, v e‖ ≤
      K * D * Real.sqrt (∑ r, ‖a r‖ ^ 2) * Real.sqrt (∑ r, ‖b r‖ ^ 2) := by
  calc
    _ ≤ ∑ e, ‖v e‖ := norm_sum_le _ _
    _ ≤ ∑ e, K * Real.sqrt (maskedEnergy mask a e) *
        Real.sqrt (maskedEnergy mask b e) := Finset.sum_le_sum fun e _ => hlocal e
    _ = K * ∑ e, Real.sqrt (maskedEnergy mask a e) *
        Real.sqrt (maskedEnergy mask b e) := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ K * (D * Real.sqrt (∑ r, ‖a r‖ ^ 2) * Real.sqrt (∑ r, ‖b r‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (coprime_mask_mass_le mask a b D hD hincidence) hK
    _ = _ := by ring

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.coprime_mask_mass_le
#print axioms Qrh.JointDetector.coprime_mask_bilinear_sum_le
