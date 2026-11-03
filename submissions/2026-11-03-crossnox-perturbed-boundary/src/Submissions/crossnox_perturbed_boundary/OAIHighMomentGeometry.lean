/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighMomentGeometry.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighData

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.PerturbedMomentTransport

variable {gap : ℝ}

def kappaPlain (_D : Parameters.PerturbedHighData gap) : ℝ := 3 / 4

theorem normalize_source_slot_geometry (D : Parameters.PerturbedHighData gap)
    (d : ℝ) (hd : (1 / 200 : ℝ) ≤ d) (hdtop : d ≤ 7 / 8) :
    (∀ j, 0 < D.ell j / d ∧ D.rmin ≤ D.ell j / d ∧
      D.ell j / d ≤ (1 + 6 * Parameters.perturbedSlotLengthShift) * D.small) ∧
    (∑ j, D.ell j / d) = (1 / 6 + Parameters.perturbedSlotLengthShift) / d ∧
    (7 / 37 : ℝ) ≤ ∑ j, D.ell j / d := by
  have hdpos : 0 < d := by linarith
  have hmesh : 0 ≤ (1 + 6 * Parameters.perturbedSlotLengthShift) * D.small := by
    exact mul_nonneg (by
      norm_num [Parameters.perturbedSlotLengthShift, AsymmetricGeometry.lengthShift])
      D.small_pos.le
  have hshift : 0 ≤ Parameters.perturbedSlotLengthShift := by
    unfold Parameters.perturbedSlotLengthShift
    norm_num
  have hsum : (∑ j, D.ell j / d) =
      (1 / 6 + Parameters.perturbedSlotLengthShift) / d := by
    rw [← Finset.sum_div, D.slots_sum]
  refine ⟨?_, hsum, ?_⟩
  · intro j
    refine ⟨div_pos (D.slots_bounds j).1 hdpos, ?_, ?_⟩
    · apply (le_div_iff₀ hdpos).mpr
      have hbound := (D.slots_bounds j).2.1
      have hrmin := D.rmin_pos
      nlinarith
    · apply (div_le_iff₀ hdpos).mpr
      simpa only [mul_comm] using (D.slots_bounds j).2.2.trans
        (mul_le_mul_of_nonneg_right hd hmesh)
  · rw [hsum]
    apply (le_div_iff₀ hdpos).mpr
    nlinarith

theorem admit_final_source_row_scale (D : Parameters.PerturbedHighData gap) :
    (1 / 200 : ℝ) ≤ AsymmetricGeometry.rowBase +
      3 * Parameters.perturbedSlotLengthShift / 2 + 3 * D.small ∧
    AsymmetricGeometry.rowBase +
      3 * Parameters.perturbedSlotLengthShift / 2 + 3 * D.small ≤ 7 / 8 := by
  refine ⟨?_, D.row_threshold⟩
  have hbase : (1 / 200 : ℝ) ≤ AsymmetricGeometry.rowBase +
      3 * Parameters.perturbedSlotLengthShift / 2 := by
    norm_num [AsymmetricGeometry.rowBase, AsymmetricGeometry.skew,
      Parameters.perturbedSlotLengthShift, AsymmetricGeometry.lengthShift]
  linarith [D.small_pos]

theorem bound_selected_source_slot_mass (D : Parameters.PerturbedHighData gap)
    (selected : Finset (Fin D.N)) :
    (∑ j ∈ selected, D.ell j) ≤ 1 / 6 + Parameters.perturbedSlotLengthShift := by
  rw [← D.slots_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
    (fun j _ _ => (D.slots_bounds j).1.le)

theorem admit_final_source_slots (D : Parameters.PerturbedHighData gap) :
    let d := AsymmetricGeometry.rowBase +
      3 * Parameters.perturbedSlotLengthShift / 2 + 3 * D.small
    (∀ j, 0 < D.ell j / d ∧ D.rmin ≤ D.ell j / d ∧
      D.ell j / d ≤ (1 + 6 * Parameters.perturbedSlotLengthShift) * D.small) ∧
    (∑ j, D.ell j / d) = (1 / 6 + Parameters.perturbedSlotLengthShift) / d ∧
    (7 / 37 : ℝ) ≤ ∑ j, D.ell j / d := by
  exact normalize_source_slot_geometry D _
    (admit_final_source_row_scale D).1 (admit_final_source_row_scale D).2

theorem normalize_selected_moment_capacity (D : Parameters.PerturbedHighData gap)
    (selected : Finset (Fin D.N)) (d m : ℝ) (hd : 0 < d) :
    2 * m + 6 * kappaPlain D * (∑ j ∈ selected, D.ell j / d) ≤ 1 ↔
      2 * d * m + (9 / 2 : ℝ) * (∑ j ∈ selected, D.ell j) ≤ d := by
  rw [← Finset.sum_div]
  have hidentity : 2 * m + 6 * kappaPlain D * ((∑ j ∈ selected, D.ell j) / d) =
      (2 * d * m + (9 / 2 : ℝ) * (∑ j ∈ selected, D.ell j)) / d := by
    unfold kappaPlain
    field_simp [hd.ne']
    ring
  rw [hidentity, div_le_one hd]

end SevenEighths.PerturbedMomentTransport

end

end OAI
