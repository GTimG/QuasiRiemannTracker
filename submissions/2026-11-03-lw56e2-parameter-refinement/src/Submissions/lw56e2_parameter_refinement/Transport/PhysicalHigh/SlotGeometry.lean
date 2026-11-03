/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/SlotGeometry.lean
Original SHA-256: 12261c22d6f8651c69b8ce90be5364702e8855e274c442c84992377501ce21ef
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection

/-!
# Variable total prime length in the physical row estimates

The upstream identities specialize the total length to 1/6. These versions
retain the total length as a parameter. They are used below in an estimate
for the actual calibrated arithmetic cube sum.
-/

namespace LW56e2.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeDetectorPhysicalSelection

theorem slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot → ℝ)
    (d total : ℝ) (hell : ∑ j ∈ slots, ell j = total) :
    (∑ j ∈ slots, ell j / d) = total / d := by
  rw [← Finset.sum_div, hell]

theorem slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot → ℝ)
    (d total : ℝ) (hd : d ≠ 0) (htotal : total ≠ 0)
    (hell : ∑ j ∈ slots, ell j = total) :
    weightedMean slots (fun j => ell j / d) g =
      (∑ j ∈ slots, ell j * g j) / total := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div, hell]
  field_simp

theorem slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot → ℝ)
    (Z d mesh total : ℝ) (hZ : 0 < Z) (hd : d ≠ 0) (htotal : 0 < total)
    (hell : ∑ j ∈ slots, ell j = total) :
    (∏ j ∈ slots, (Z ^ (ell j)) ^ (-(4 / 25 : ℝ) + g j + mesh)) =
      Z ^ (-(4 / 25 : ℝ) * total +
        weightedMean slots (fun j => ell j / d) g * total + mesh * total) := by
  simp_rw [← Real.rpow_mul hZ.le]
  rw [← Real.rpow_sum_of_pos hZ]
  congr 1
  rw [slot_weightedMean slots ell g d total hd htotal.ne' hell]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hell, div_mul_cancel₀ _ htotal.ne']
  ring

end
end LW56e2.Transport.PhysicalHigh
