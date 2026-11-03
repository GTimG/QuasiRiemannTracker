/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighSlotEstimate.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighGlobalCorrection
import Submissions.crossnox_perturbed_boundary.OAIHighEulerRegion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSlotEstimate

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex

namespace SevenEighths.PrincipalSlotEstimate
open ProbeEuler ProbeLocal

def perturbedBoundary : ℝ := boundary

theorem bound_region_correction_defect_on_perturbed_boundary
    {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hs : perturbedBoundary ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hb := PerturbedZeroFreeBound.bound_unramified_closed_on_perturbed_region
    Q A η 1 s w z (by linarith) hA hη (by simp)
    (by simpa only [perturbedBoundary] using hs) hw hz
  have hp : Q ^ (-(363 / 200 : ℝ) + 6 * boundaryReduction) ≤ Q ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hi : 240 * Q ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
    exact (div_le_iff₀ hQ0).mpr (by linarith)
  exact hb.trans ((mul_le_mul_of_nonneg_left hp (by norm_num)).trans hi)

theorem bound_region_correction_inverse_on_perturbed_boundary
    {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hs : perturbedBoundary ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hb := bound_region_correction_defect_on_perturbed_boundary
    hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  have hl : 1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by linarith
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr
    (by linarith)

theorem bound_region_geometric_factors_on_perturbed_boundary
    {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1)
    (hs : perturbedBoundary ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans
      (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q _ hQ4 (by simp only [perturbedBoundary, boundary] at hs; linarith))

theorem bound_region_marked_error_on_perturbed_boundary
    {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1)
    (hs : perturbedBoundary ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-perturbedBoundary) ∧
    ‖star η * (Q : ℂ) ^ s‖ *
      ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-perturbedBoundary) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := principal_B_norm hQ0 η s hη
  have hg := bound_region_geometric_factors_on_perturbed_boundary hQ hη.le hs hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4
      (by simp only [perturbedBoundary, boundary] at hs; linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-perturbedBoundary) :=
    hR.trans (hpow _ _ (by simp only [perturbedBoundary, boundary] at hs ⊢; linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤
      Q ^ (-perturbedBoundary) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0]
        congr 1
        ring
      _ ≤ _ := hpow _ _ (by simp only [perturbedBoundary, boundary] at hs ⊢; linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤
      Q ^ (-perturbedBoundary) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0]
        congr 1
        ring
      _ ≤ _ := hpow _ _ (by simp only [perturbedBoundary, boundary] at hs ⊢; linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤ Q ^ (-perturbedBoundary) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by
        rw [hB, hV]
        gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
        congr 1
        ring
      _ ≤ _ := hpow _ _ (by simp only [perturbedBoundary, boundary] at hs ⊢; linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ +
        4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE'
      (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem bound_region_replacement_error_on_perturbed_boundary
    {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1)
    (hs : perturbedBoundary ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-perturbedBoundary) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := bound_region_geometric_factors_on_perturbed_boundary hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-perturbedBoundary) := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1
      (by simp only [perturbedBoundary, boundary]; linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-perturbedBoundary) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := bound_region_marked_error_on_perturbed_boundary hQ hA hη hs hw hz
  exact compensated_unit_error_bound _ _ _ _ _ _ _
    (Real.rpow_nonneg hQ0.le _) hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem bound_region_slot_error_on_perturbed_boundary
    {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1)
    (hs : perturbedBoundary ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤
      1440 * Q ^ (-perturbedBoundary) := by
  have hb := bound_region_correction_defect_on_perturbed_boundary
    hQ hA hη.le hs hw hz
  have hne : unramifiedClosed Q A η 1 s w z ≠ 0 := by
    apply norm_pos_iff.mp
    have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
    rw [norm_one, norm_sub_rev] at hn
    linarith
  have he := bound_region_replacement_error_on_perturbed_boundary
    hQ hA hη hs hw hz
  have hi := bound_region_correction_inverse_on_perturbed_boundary
    hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-perturbedBoundary)) * 2 :=
      mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem bound_region_slot_norm_on_perturbed_boundary
    {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1)
    (hs : perturbedBoundary ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤
      1 + 1440 * Q ^ (-perturbedBoundary) := by
  have he := bound_region_slot_error_on_perturbed_boundary
    hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem bound_weighted_region_slots_on_perturbed_boundary
    {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : perturbedBoundary ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) *
      regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-perturbedBoundary)) *
        ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) *
        regionSlot (Q i) (A i) (η i) s w z‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-perturbedBoundary)) *
        (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := bound_region_slot_norm_on_perturbed_boundary
        (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤
          1 + 1440 * P ^ (-perturbedBoundary) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi)
          (by unfold perturbedBoundary; norm_num)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hb i hi), Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq
          (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

end SevenEighths.PrincipalSlotEstimate

end

end OAI
