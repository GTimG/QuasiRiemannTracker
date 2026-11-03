/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighComplexSlotBounds.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighFiniteProductWZ
import Submissions.crossnox_perturbed_boundary.OAIHighFiniteProductBounds

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex Set
namespace SevenEighths.ProbeFiniteProductBounds

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

private theorem bound_marked_on_perturbed_boundary
    (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  norm_num [AsymmetricGeometry.boundary] at hx
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1 / 2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans
      (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1
      (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1 / 2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1
      (by linarith : 1 - x.re - w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x)
    hR hV hqi hD
  have h1 : 12 * ‖coordR Q A x z‖ * (1 + ‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12 * (1 / 2 : ℝ) * (1 + 1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4 * ‖coordK Q η x w‖ * ‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4 * 1 * (1 / 2 : ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le
    (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

theorem bound_local_multiplier_with_complex_weight_on_perturbed_boundary
    (η : Character) (S : Finset Id) (hS : PerturbedCorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (AsymmetricGeometry.boundary : ℝ) Bx)
    (hw : (19 / 20 : ℝ) ≤ w.re)
    (hz : z.re ∈ Icc (33 / 200 : ℝ) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  have hxLower := hx.1
  norm_num [AsymmetricGeometry.boundary] at hxLower
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by
    dsimp [Q]
    exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val) * (Q : ℂ) ^ x‖ ≤ Q ^ Bx := by
    rw [norm_mul, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _)
      (idealCoeff_norm_le_one η _)).trans
        (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0, Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1
      (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    simpa only [coordW, one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1 / 2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    bound_marked_on_perturbed_boundary Q
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val)
      x w z hQ (actualAPhase_norm_le_one η _)
      (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound _ _ _ _ _ _ (Q ^ Bx)
    (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hd := bound_ideal_closed_correction_on_perturbed_region
    η P (hS.norm_four P hP) x w z hx.1 (by linarith) (by linarith [hz.1])
  have hsingle := hS.bound_single_defect ⟨P, hP⟩
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  have hnorm : 1 / 2 ≤ ‖idealClosedCorrection η P x w z‖ := by linarith
  have hi : ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div]
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hp : ‖(Q : ℂ) ^ (z - 1)‖ ≤ Q ^ (Bz - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re, Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  change _ ≤ Q ^ (Bz - 1) * (400 * (1 + Q ^ Bx))
  calc
    _ ≤ Q ^ (Bz - 1) * (200 * (1 + Q ^ Bx) * 2) := by gcongr
    _ = _ := by ring

theorem bound_slot_multiplier_with_complex_weight_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id) (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (AsymmetricGeometry.boundary : ℝ) Bx)
    (hw : (19 / 20 : ℝ) ≤ w.re)
    (hz : z.re ∈ Icc (33 / 200 : ℝ) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier, slotBound, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (bound_local_multiplier_with_complex_weight_on_perturbed_boundary
      η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

theorem bound_combined_slots_with_complex_weight_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id) (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (AsymmetricGeometry.boundary : ℝ) Bx)
    (hw : (19 / 20 : ℝ) ≤ w.re)
    (hz : z.re ∈ Icc (33 / 200 : ℝ) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3 / 2) * slotBound J T b Bx Bz := by
  have hglobal := bound_global_closed_correction_on_perturbed_region
    η S hS x w z hx.1 (by linarith) (by linarith [hz.1])
  have htriangle := norm_add_le (globalClosedCorrection η S x w z - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at htriangle
  have hg : ‖globalClosedCorrection η S x w z‖ ≤ 3 / 2 := by linarith
  rw [norm_mul]
  exact mul_le_mul hg
    (bound_slot_multiplier_with_complex_weight_on_perturbed_boundary
      η S hS J T b hT x w z Bx Bz hx hw hz)
    (norm_nonneg _) (by norm_num)

end SevenEighths.ProbeFiniteProductBounds

end

end OAI
