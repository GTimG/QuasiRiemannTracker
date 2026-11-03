/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighFiniteProductWZ.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighFixedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductBounds

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma marked_differentiableAt_w_on_perturbed_boundary
    (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ))
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := perturbed_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0
    (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma marked_differentiableAt_z_on_perturbed_boundary
    (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ))
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := perturbed_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_w_on_perturbed_boundary
    (η : Character) (S : Finset Id) (hS : PerturbedCorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z)
      {w : ℂ | 9 / 10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := perturbed_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hx hz
  have hc := unramified_closed_analytic_w_on_perturbed_region
    (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := marked_differentiableAt_w_on_perturbed_boundary
    η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ
      (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hdefect := bound_ideal_closed_correction_on_perturbed_region
    η P (hS.norm_four P hP) x w z hx hw.le hz
  have hhalf := hS.bound_single_defect ⟨P, hP⟩
  have hh : idealClosedCorrection η P x w z ≠ 0 := by
    apply norm_pos_iff.mp
    have hnorm := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
    rw [norm_one, norm_sub_rev] at hnorm
    linarith
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem local_analytic_z_on_perturbed_boundary
    (η : Character) (S : Finset Id) (hS : PerturbedCorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z)
      {z : ℂ | 4 / 25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramified_closed_analytic_z_on_perturbed_region
    (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := perturbed_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hx hz.le
  have hmc := marked_differentiableAt_z_on_perturbed_boundary
    η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ
      (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hdefect := bound_ideal_closed_correction_on_perturbed_region
    η P (hS.norm_four P hP) x w z hx hw hz.le
  have hhalf := hS.bound_single_defect ⟨P, hP⟩
  have hh : idealClosedCorrection η P x w z ≠ 0 := by
    apply norm_pos_iff.mp
    have hnorm := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
    rw [norm_one, norm_sub_rev] at hnorm
    linarith
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem slot_analytic_w_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z)
      {w : ℂ | 9 / 10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul
    (local_analytic_w_on_perturbed_boundary η S hS P (hT j hj P hp) x z hx hz)

theorem slot_analytic_z_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z)
      {z : ℂ | 4 / 25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul
    (local_analytic_z_on_perturbed_boundary η S hS P (hT j hj P hp) x w hx hw)

theorem combined_slot_analytic_w_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ
      (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9 / 10 < w.re} :=
  (global_closed_correction_analytic_w_on_perturbed_region η S hS x z hx hz).mul
    (slot_analytic_w_on_perturbed_boundary η S hS J T b hT x z hx hz)

theorem combined_slot_analytic_z_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) :
    AnalyticOnNhd ℂ
      (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4 / 25 < z.re} :=
  (global_closed_correction_analytic_z_on_perturbed_region η S hS x w hx hw).mul
    (slot_analytic_z_on_perturbed_boundary η S hS J T b hT x w hx hw)

end SevenEighths.ProbeFiniteProductBounds

end

end OAI
