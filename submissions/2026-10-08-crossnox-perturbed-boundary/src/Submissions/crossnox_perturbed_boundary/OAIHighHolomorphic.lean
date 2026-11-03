/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighHolomorphic.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighRamifiedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma perturbed_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (boundary : ℝ) ≤ x.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    1 - coordR Q A x z ≠ 0 ∧ 1 - coordV Q z ≠ 0 ∧
      1 - coordD Q eta v x ≠ 0 := by
  norm_num [boundary] at hx
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
    apply (coordD_norm_le Q hQ0 eta v x heta hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramified_closed_analytic_x_on_perturbed_region
    (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => unramifiedClosed Q A eta v x w z)
      {x : ℂ | boundary < x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := perturbed_region_denominators Q A eta v x z hQ hA heta hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramified_closed_analytic_w_on_perturbed_region
    (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (boundary : ℝ) ≤ x.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => unramifiedClosed Q A eta v x w z)
      {w : ℂ | 9 / 10 < w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := perturbed_region_denominators Q A eta v x z hQ hA heta hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramified_closed_analytic_z_on_perturbed_region
    (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (boundary : ℝ) ≤ x.re) :
    AnalyticOnNhd ℂ (fun z => unramifiedClosed Q A eta v x w z)
      {z : ℂ | 4 / 25 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := perturbed_region_denominators Q A eta v x z hQ hA heta hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

theorem ramified_closed_analytic_x_on_perturbed_region
    (eta a rho w z : ℂ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (ha : ‖a‖ ≤ 1) (hz : (4 / 25 : ℝ) ≤ z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x => ramifiedClosed p hp hg eta a rho x w z j)
      {x : ℂ | boundary < x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := perturbed_region_denominators _ (a ^ 2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)
    (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id
    (fun _ => w) (fun _ => z) x differentiableAt_id
    (differentiableAt_const w) (differentiableAt_const z)
    hd.2.1 hd.1 j).differentiableWithinAt

theorem ramified_closed_analytic_w_on_perturbed_region
    (eta a rho x z : ℂ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (ha : ‖a‖ ≤ 1) (hx : (boundary : ℝ) ≤ x.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) (j : ℕ) :
    Differentiable ℂ (fun w => ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := perturbed_region_denominators _ (a ^ 2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)
    (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho
    (fun _ => x) id (fun _ => z) w (differentiableAt_const x)
    differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

theorem ramified_closed_analytic_z_on_perturbed_region
    (eta a rho x w : ℂ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (ha : ‖a‖ ≤ 1) (hx : (boundary : ℝ) ≤ x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z => ramifiedClosed p hp hg eta a rho x w z j)
      {z : ℂ | 4 / 25 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := perturbed_region_denominators _ (a ^ 2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)
    (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho
    (fun _ => x) (fun _ => w) id z (differentiableAt_const x)
    (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end SevenEighths.ProbeEuler

end

end OAI
