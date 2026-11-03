/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalAnalytic/GlobalCorrection.lean
Original SHA-256: 148b0720e9c29161838ef9e98cee090c5bd912352c14b79017d58dbfb17b2adb
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.LocalBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.GlobalCorrection

/-!
# The actual multivariable Euler correction on a transported domain

This extends the pinned OpenAI broad Euler region in its x coordinate.
For p<1/1000 the old defect envelope 240 Q^(-17/10) still works; thus
no new tail condition is needed for the source's literal global correction.
The proof adapts OpenAI's coordinate-bound and normal-product arguments.
-/

namespace LW56e2.Transport.PhysicalAnalytic
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic ProbeEuler ProbePhysical CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem unramifiedClosed_transported_open_region_bound
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  dsimp [Geometry.boundary] at hx
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(221/100:ℝ) + 3*p/2) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7/8:ℝ) + p/4) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(31/40:ℝ) + p/4) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by linarith))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by linarith)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by linarith)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by linarith)
      _ = _ := by ring
  nlinarith

theorem transported_open_region_denominators
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    1 - coordR Q A x z ≠ 0 ∧ 1 - coordV Q z ≠ 0 ∧
      1 - coordD Q eta v x ≠ 0 := by
  dsimp [Geometry.boundary] at hx
  have hQ0 : 0 < Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1 / 2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖ ≤ 1 / 2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramifiedClosed_transported_analytic_x
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => unramifiedClosed Q A eta v x w z)
      {x : ℂ | Geometry.boundary p < x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := transported_open_region_denominators p hp Q A eta v x z
    hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_transported_analytic_w
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => unramifiedClosed Q A eta v x w z)
      {w : ℂ | (9 / 10 : ℝ) < w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w _
  have hd := transported_open_region_denominators p hp Q A eta v x z
    hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_transported_analytic_z
    (p : ℝ) (hp : p < 1 / 1000) (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : Geometry.boundary p ≤ x.re) :
    AnalyticOnNhd ℂ (fun z => unramifiedClosed Q A eta v x w z)
      {z : ℂ | (4 / 25 : ℝ) < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := transported_open_region_denominators p hp Q A eta v x z
    hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem idealClosedCorrection_transported_bound
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : Geometry.boundary p ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    ‖idealClosedCorrection η P x w z - 1‖ ≤ globalPrimeDefectBound P := by
  apply unramifiedClosed_transported_open_region_bound p hp
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_transported_bound
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ) (hx : Geometry.boundary p ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    ‖globalClosedCorrection η S x w z - 1‖ ≤ (1 / 2 : ℝ) :=
  product_defect_le _ _ hS.summable
    (fun P => idealClosedCorrection_transported_bound p hp η P.val
      (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

theorem globalClosedCorrection_transported_analytic_x
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z)
      {x : ℂ | Geometry.boundary p < x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_transported_analytic_x p hp
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_transported_bound p hp η P.val
      (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem globalClosedCorrection_transported_analytic_w
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ)
    (hx : Geometry.boundary p ≤ x.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z)
      {w : ℂ | (9 / 10 : ℝ) < w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_transported_analytic_w p hp
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_transported_bound p hp η P.val
      (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem globalClosedCorrection_transported_analytic_z
    (p : ℝ) (hp : p < 1 / 1000) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ)
    (hx : Geometry.boundary p ≤ x.re) (hw : (9 / 10 : ℝ) ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z)
      {z : ℂ | (4 / 25 : ℝ) < z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_transported_analytic_z p hp
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_transported_bound p hp η P.val
      (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

end
end LW56e2.Transport.PhysicalAnalytic
