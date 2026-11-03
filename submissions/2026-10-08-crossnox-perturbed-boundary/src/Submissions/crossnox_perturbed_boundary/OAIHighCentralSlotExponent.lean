/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighCentralSlotExponent.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma perturbed_slot_length_sum {Slot : Type*} (slots : Finset Slot)
    (ell : Slot → ℝ) (d t : ℝ)
    (hell : ∑ j ∈ slots, ell j = 1 / 6 + t) :
    (∑ j ∈ slots, ell j / d) = (1 / 6 + t) / d := by
  rw [← Finset.sum_div, hell]

lemma perturbed_slot_weightedMean {Slot : Type*} (slots : Finset Slot)
    (ell g : Slot → ℝ) (d t : ℝ) (hd : d ≠ 0)
    (hL : 1 / 6 + t ≠ 0)
    (hell : ∑ j ∈ slots, ell j = 1 / 6 + t) :
    weightedMean slots (fun j => ell j / d) g =
      (∑ j ∈ slots, ell j * g j) / (1 / 6 + t) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div, hell]
  field_simp [hL, hd]

lemma perturbed_slot_product {Slot : Type*} (slots : Finset Slot)
    (ell g : Slot → ℝ) (Z d mesh t : ℝ) (hZ : 0 < Z)
    (hd : d ≠ 0) (hL : 1 / 6 + t ≠ 0)
    (hell : ∑ j ∈ slots, ell j = 1 / 6 + t) :
    (∏ j ∈ slots, (Z ^ (ell j)) ^ (-(4 / 25 : ℝ) + g j + mesh)) =
      Z ^ ((1 / 6 + t) * (-(4 / 25 : ℝ) +
        weightedMean slots (fun j => ell j / d) g + mesh)) := by
  simp_rw [← Real.rpow_mul hZ.le]
  rw [← Real.rpow_sum_of_pos hZ]
  congr 1
  have hweighted := perturbed_slot_weightedMean slots ell g d t hd hL hell
  have hsum :
      (1 / 6 + t) * weightedMean slots (fun j => ell j / d) g =
        ∑ j ∈ slots, ell j * g j := by
    rw [hweighted]
    exact mul_div_cancel₀ _ hL
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hell]
  rw [← hsum]

end SevenEighths.ProbeHighRowFamily

end

end OAI
