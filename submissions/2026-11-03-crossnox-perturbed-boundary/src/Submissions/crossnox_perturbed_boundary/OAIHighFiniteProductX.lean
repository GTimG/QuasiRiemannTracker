/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighFiniteProductX.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighFiniteProductBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductX

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductX

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma marked_differentiableAt_x_on_perturbed_boundary
    (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ))
    (hx : (AsymmetricGeometry.boundary : ℝ) ≤ x.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := perturbed_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0
    (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0
    (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x_on_perturbed_boundary
    (η : Character) (S : Finset Id) (hS : PerturbedCorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z)
      {x : ℂ | AsymmetricGeometry.boundary < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramified_closed_analytic_x_on_perturbed_region
    (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := perturbed_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _)
    (by simp) hx.le hz
  have hm := marked_differentiableAt_x_on_perturbed_boundary
    η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ
      (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hdefect := bound_ideal_closed_correction_on_perturbed_region
    η P (hS.norm_four P hP) x w z hx.le hw hz
  have hhalf := hS.bound_single_defect ⟨P, hP⟩
  have hh : idealClosedCorrection η P x w z ≠ 0 := by
    apply norm_pos_iff.mp
    have hnorm := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
    rw [norm_one, norm_sub_rev] at hnorm
    linarith
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0
    (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem slot_analytic_x_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z)
      {x : ℂ | AsymmetricGeometry.boundary < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul
    (local_analytic_x_on_perturbed_boundary η S hS P (hT j hj P hp) w z hw hz)

theorem combined_slot_analytic_x_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ
      (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | AsymmetricGeometry.boundary < x.re} :=
  (global_closed_correction_analytic_x_on_perturbed_region η S hS w z hw hz).mul
    (slot_analytic_x_on_perturbed_boundary η S hS J T b hT w z hw hz)

theorem continued_source_analytic_x_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0 < Z) (w z : ℂ)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ
      (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (AsymmetricGeometry.boundary : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (AsymmetricGeometry.boundary : ℝ) < x.re :=
    lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta < x.re :=
    lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (global_closed_correction_analytic_x_on_perturbed_region
    η S hTail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x_on_perturbed_boundary
    η S hTail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt
    (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_differentiable_strip_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0 < Z) (w z : ℂ)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re)
    {a c : ℝ} (ha : AsymmetricGeometry.boundary < a)
    (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ
      (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a ≤ x.re ∧ x.re ≤ c} := by
  apply (continued_source_analytic_x_on_perturbed_boundary
    η S hS hTail J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

end SevenEighths.ProbeFiniteProductX

end

end OAI
