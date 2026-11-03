/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighEulerRegion.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.EulerRegion

open OAI.SevenEighths.AsymmetricGeometry
namespace PerturbedZeroFreeBound

noncomputable section

open OAI.SevenEighths.ProbeEuler

theorem bound_unramified_closed_on_perturbed_region
    (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (boundary : ℝ) ≤ x.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤
      240 * Q ^ (-(363 / 200 : ℝ) + 6 * boundaryReduction) := by
  rw [verify_boundary] at hx
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(99 / 100 : ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(56 / 25 : ℝ) + 6 * boundaryReduction) :=
    (coordR_norm_le Q hQ0 A x z hA).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(19 / 20 : ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7 / 8 : ℝ) + boundaryReduction) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(33 / 40 : ℝ) + boundaryReduction) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVhalf : ‖V‖ ≤ 1 / 2 := hV.trans
    (rpow_le_half Q _ hQ (by norm_num))
  have hRhalf : ‖R‖ ≤ 1 / 2 := hR.trans
    (rpow_le_half Q _ hQ (by norm_num))
  have hDhalf : ‖D‖ ≤ 1 / 2 := hD.trans
    (rpow_le_half Q _ hQ (by norm_num))
  have hWone : ‖W‖ ≤ 1 := hW.trans
    ((Real.rpow_le_rpow_of_exponent_le hQ1
      (by norm_num : -(19 / 20 : ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hQinv : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(363 / 200 : ℝ) + 6 * boundaryReduction)
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b exponentA exponentB : ℝ)
      (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q ^ exponentA) (hbb : b ≤ Q ^ exponentB)
      (hexponents : exponentA + exponentB ≤ -(363 / 200 : ℝ) + 6 * boundaryReduction) :
      a * b ≤ T := by
    calc
      a * b ≤ Q ^ exponentA * Q ^ exponentB :=
        mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (exponentA + exponentB) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 hexponents
  have hKV : ‖K‖ * ‖V‖ ≤ T :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖ * ‖V‖ ≤ T :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖ * ‖W‖ ≤ T :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖ * ‖W‖ ≤ T :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖ * ‖V‖ * ‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWone).trans hDV
  let P := markedFactor R V (Q : ℂ)⁻¹ K (-D + W * R) 1
  have hE : ‖P + D‖ ≤ 28 * T := by
    have h := OAI.SevenEighths.ProbeLocal.unramified_marked_error_bound
      R V (Q : ℂ)⁻¹ K W D hRhalf hVhalf hQinv hDhalf
    have hRterm : ‖R‖ * (1 + ‖W‖) ≤ 2 * T := by
      calc
        _ ≤ ‖R‖ * 2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := OAI.SevenEighths.ProbeLocal.continuedCorrection_defect_bound
    V W D P hVhalf hDhalf
  change ‖OAI.SevenEighths.ProbeLocal.continuedCorrection V W D P - 1‖ ≤ 240 * T
  have hWE : (1 + ‖W‖) * ‖P + D‖ ≤ 56 * T := by
    calc
      _ ≤ 2 * (28 * T) :=
        mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

end

end PerturbedZeroFreeBound
