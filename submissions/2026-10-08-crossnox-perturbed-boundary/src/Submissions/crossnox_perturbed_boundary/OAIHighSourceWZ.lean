/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighSourceWZ.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighFiniteProductWZ
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductBounds

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem source_multiplier_differentiable_w_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0 < a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hY : 0 < Y) (s z : ℂ)
    (hs : (boundary : ℝ) ≤ s.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    DifferentiableOn ℂ
      (fun w => sourceMultiplier W0 W1 X Y Z
        (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z)
      {w : ℂ | 9 / 10 < w.re} := by
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable
    W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (combined_slot_analytic_w_on_perturbed_boundary
    η S hTail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he :
      (fun w => sourceMultiplier W0 W1 X Y Z
        (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
      (fun w => ((X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) *
        Complex.exp ((s + z - 1) ^ 2) *
        mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z /
        LFunction (η.excludePrimes S hS.prime) s) *
        (Y : ℂ) ^ (w - 1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w
    unfold sourceMultiplier
    ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem source_multiplier_differentiable_z_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (hX : 0 < X) (hZ : 0 < Z) (s w : ℂ)
    (hs : (boundary : ℝ) ≤ s.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) :
    DifferentiableOn ℂ
      (fun z => sourceMultiplier W0 W1 X Y Z
        (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z)
      {z : ℂ | 4 / 25 < z.re} := by
  have hM : DifferentiableOn ℂ
      (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4 / 25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono
      (by intro z hz; change 0 < z.re; change (4 / 25 : ℝ) < z.re at hz; linarith)
  have hH := (combined_slot_analytic_z_on_perturbed_boundary
    η S hTail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he :
      (fun z => sourceMultiplier W0 W1 X Y Z
        (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
      (fun z => ((Y : ℂ) ^ (w - 1) * mellin W1 w /
        LFunction (η.excludePrimes S hS.prime) s) *
        (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) *
        Complex.exp ((s + z - 1) ^ 2) *
        mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z
    unfold sourceMultiplier
    ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

end SevenEighths.ProbeFiniteProductBounds

end

end OAI
