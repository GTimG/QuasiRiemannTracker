/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighXTransport.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighResidueMoments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalTransport

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalTransport

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem principal_box_majorant_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a) (hξlo : 1 / 6 < ξlo) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ σ ∈ Icc a 3, ∀ ξ ∈ Icc ξlo 2, ∀ p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ : ℂ) + p.1.1 * I) ((3 : ℂ) + p.2 * I)
        ((ξ : ℂ) + p.1.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + p.1.2 * I)) *
        LFunction (fixedSourcePrincipal S hS.prime)
          ((3 : ℂ) + p.2 * I)‖ ≤ A * jointEnvelope 8 p := by
  norm_num [boundary] at ha
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D, hD, hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay
    W0 a0 b0 ha0 hW0 ξlo 2 (by linarith) 10
  obtain ⟨E, hE, he⟩ :=
    CubicReflectionKernel.compact_source_mellin_strip_decay
      W1 a1 b1 ha1 hW1 (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C
    2 (6 * ξlo - 1)
  let B := realGaussianBound a 3 ξlo 2 * 2 ^ 8 * D * E
  have hA : 0 ≤ A := arithmeticAmplitude_nonneg
    S hS.prime J T b X Y Z a 3 2 3 C 2 (6 * ξlo - 1)
      (by norm_num) hC (by norm_num) (by linarith)
  have hB : 0 ≤ B := by
    dsimp [B]
    have := (realGaussianBound_pos a 3 ξlo 2).le
    positivity
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ ∈ Icc (33 / 200 : ℝ) 2 :=
    ⟨by linarith [hξ.1], hξ.2⟩
  have hw : (2 : ℝ) ≤ ‖((3 : ℂ) + p.2 * I) - 1‖ := by
    convert pole_distance_vertical 1 3 p.2 using 1
    norm_num
  have hz : 6 * ξlo - 1 ≤
      ‖6 * ((ξ : ℂ) + p.1.2 * I) - 1‖ := by
    have h := Complex.abs_re_le_norm
      (6 * ((ξ : ℂ) + p.1.2 * I) - 1)
    have hh : 0 ≤ 6 * ξ - 1 := by linarith [hξ.1]
    simp only [sub_re, mul_re, ofReal_re, ofReal_im, add_re,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, one_re] at h
    norm_num only [show (6 : ℂ).re = 6 by norm_num,
      show (6 : ℂ).im = 0 by norm_num, zero_mul, sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [hξ.1]) h
  have hb := bound_arithmetic_on_lines_with_gaps_on_perturbed_region
    η S hS hTail J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num)
    2 (6 * ξlo - 1) (by norm_num) (by linarith) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le
    (hd ξ hξ) (he 3 ⟨le_rfl, le_rfl⟩) p
  rw [← arithmetic_profile_eq_source, norm_mul]
  calc
    _ ≤ (A * jointHeight p.1.1 p.1.2 p.2 ^ 8) *
        ‖profile W0 W1 ((σ : ℂ) + p.1.1 * I)
          ((3 : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A * (jointHeight p.1.1 p.1.2 p.2 ^ 8 *
        ‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines, ofReal_ofNat]
      ring
    _ ≤ A * (B * jointEnvelope 8 p) :=
      mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem continued_x_shift_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) < a) (ha3 : a ≤ 3)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 1 / 6 < ξ) (hξ2 : ξ ≤ 2) (v u : ℝ) :
    verticalIntegral a (fun s =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        s ((3 : ℂ) + u * I) ((ξ : ℂ) + v * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((ξ : ℂ) + v * I)) *
      LFunction (fixedSourcePrincipal S hS.prime)
        ((3 : ℂ) + u * I)) =
    verticalIntegral 3 (fun s =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        s ((3 : ℂ) + u * I) ((ξ : ℂ) + v * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((ξ : ℂ) + v * I)) *
      LFunction (fixedSourcePrincipal S hS.prime)
        ((3 : ℂ) + u * I)) := by
  norm_num [boundary] at ha
  obtain ⟨A, hA, hb⟩ := principal_box_majorant_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := continued_source_differentiable_strip_on_perturbed_boundary
    η S hS hTail J T b hT W0 W1 X Y Z hZ
    ((3 : ℂ) + u * I) ((ξ : ℂ) + v * I)
    (by norm_num) (by simpa using
      (show (4 / 25 : ℝ) ≤ ξ by linarith)) ha hβ (c := 3)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A := A * cauchy v * cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl, hξ2⟩ ((t, v), u)
  simpa only [jointEnvelope, Prod.fst, Prod.snd, mul_assoc,
    mul_left_comm, mul_comm] using h

end SevenEighths.ProbePrincipalTransport

end

end OAI
