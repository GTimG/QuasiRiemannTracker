/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighZTransport.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighXTransport

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

theorem continued_source_differentiable_z_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (hX : 0 < X) (hZ : 0 < Z)
    (s w : ℂ) (hs : (boundary : ℝ) ≤ s.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) :
    DifferentiableOn ℂ
      (fun z => continuedSourceMultiplier η S hS.prime J T b
        W0 W1 X Y Z s w z) {z : ℂ | 4 / 25 < z.re} := by
  have hM : DifferentiableOn ℂ
      (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4 / 25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono
      (by intro z hz
          change 0 < z.re
          change (4 / 25 : ℝ) < z.re at hz
          linarith)
  have hH := (combined_slot_analytic_z_on_perturbed_boundary
    η S hTail J T b hT s w hs hw).differentiableOn
  have hnX : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hnZ : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b
      W0 W1 X Y Z s w z) =
    (fun z => ((Y : ℂ) ^ (w - 1) * mellin W1 w *
      HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s) *
      (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) *
      Complex.exp ((s + z - 1) ^ 2) *
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z *
      (globalClosedCorrection η S s w z *
        slotMultiplier η J T b s w z)) := by
    funext z
    unfold continuedSourceMultiplier
    ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

theorem continued_principal_differentiable_z_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (hX : 0 < X) (hZ : 0 < Z)
    (s w : ℂ) (hs : (boundary : ℝ) ≤ s.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) :
    DifferentiableOn ℂ
      (fun z => continuedSourceMultiplier η S hS.prime J T b
        W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
        LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1 / 6 < z.re} := by
  have hK := continued_source_differentiable_z_on_perturbed_region
    η S hS hTail J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by
      intro z hz
      change (4 / 25 : ℝ) < z.re
      change (1 / 6 : ℝ) < z.re at hz
      linarith)).mul ?_).mul_const
  intro z hz
  have h0 : (6 * z : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    change (1 / 6 : ℝ) < z.re at hz
    linarith
  have h1 : (6 * z : ℂ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    change (1 / 6 : ℝ) < z.re at hz
    linarith
  exact ((LFunction_differentiableAt
    (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
      (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem continued_z_shift_on_perturbed_region
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
    (ha : (boundary : ℝ) ≤ a) (ha3 : a ≤ 3)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 1 / 6 < ξ) (hξ2 : ξ ≤ 2) (t u : ℝ) :
    verticalIntegral ξ (fun z =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a : ℂ) + t * I) ((3 : ℂ) + u * I) z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
      LFunction (fixedSourcePrincipal S hS.prime)
        ((3 : ℂ) + u * I)) =
    verticalIntegral 2 (fun z =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a : ℂ) + t * I) ((3 : ℂ) + u * I) z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
      LFunction (fixedSourcePrincipal S hS.prime)
        ((3 : ℂ) + u * I)) := by
  obtain ⟨A, hA, hb⟩ := principal_box_majorant_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := continued_principal_differentiable_z_on_perturbed_region
    η S hS hTail J T b hT W0 W1 X Y Z hX hZ
    ((a : ℂ) + t * I) ((3 : ℂ) + u * I)
    (by simpa using ha) (by norm_num)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by
      intro z hz
      change (1 / 6 : ℝ) < z.re
      exact hξ.trans_le hz.1)) (A := A * cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl, ha3⟩ ζ hζ ((t, v), u)
  calc
    _ ≤ A * (gaussianMoment 8 (t + v) * cauchy v * cauchy u) := h
    _ ≤ A * (gaussianMoment 8 (t + v) * 1 * cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t + v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

end SevenEighths.ProbePrincipalTransport

end

end OAI
