/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighFiniteProductBounds.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighSlotEstimate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeFiniteProductBounds

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem bound_slot_multiplier_on_perturbed_boundary
    {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀ j ∈ J, ∀ P ∈ T j, 0 ≤ b j P)
    (hQ : ∀ j ∈ J, ∀ P ∈ T j, Pmin ≤ (Ideal.absNorm P.val : ℝ))
    (hη : ∀ j ∈ J, ∀ P ∈ T j, ‖idealCoeff η P.val‖ = 1)
    (s w z : ℂ) (hs : (AsymmetricGeometry.boundary : ℝ) ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1 + 1440 * Pmin ^ (-(AsymmetricGeometry.boundary : ℝ))) *
        ∑ P ∈ T j, b j P * (Ideal.absNorm P.val : ℝ) ^ (z.re - 1) := by
  simp only [slotMultiplier, local_eq_regionSlot, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [PrincipalSlotEstimate.perturbedBoundary, mul_assoc,
    Complex.ofReal_natCast] using
    PrincipalSlotEstimate.bound_weighted_region_slots_on_perturbed_boundary
      (T j) (b j) (fun P => (Ideal.absNorm P.val : ℝ))
      (fun P => actualAPhase η (primaryGenerator P.val))
      (fun P => idealCoeff η P.val) s w z Pmin hPmin
      (hb j hj) (hQ j hj) (fun P _ => actualAPhase_norm_le_one η _)
      (hη j hj) hs hw hz

theorem bound_combined_slots_on_perturbed_boundary
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀ j ∈ J, ∀ P ∈ T j, 0 ≤ b j P)
    (hQ : ∀ j ∈ J, ∀ P ∈ T j, Pmin ≤ (Ideal.absNorm P.val : ℝ))
    (hη : ∀ j ∈ J, ∀ P ∈ T j, ‖idealCoeff η P.val‖ = 1)
    (s w z : ℂ) (hs : (AsymmetricGeometry.boundary : ℝ) ≤ s.re)
    (hw : (19 / 20 : ℝ) ≤ w.re) (hz : (33 / 200 : ℝ) ≤ z.re) :
    ‖globalClosedCorrection η S s w z *
      slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3 / 2) * ∏ j ∈ J,
        (1 + 1440 * Pmin ^ (-(AsymmetricGeometry.boundary : ℝ))) *
          ∑ P ∈ T j, b j P * (Ideal.absNorm P.val : ℝ) ^ (z.re - 1) := by
  have hglobal := bound_global_closed_correction_on_perturbed_region
    η S hS s w z hs (by linarith) (by linarith)
  have hgnorm : ‖globalClosedCorrection η S s w z‖ ≤ 3 / 2 := by
    have htriangle := norm_add_le
      (globalClosedCorrection η S s w z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at htriangle
    linarith
  have hslots := bound_slot_multiplier_on_perturbed_boundary
    η J T b Pmin hPmin hb hQ hη s w z hs hw hz
  rw [norm_mul]
  exact mul_le_mul hgnorm hslots (norm_nonneg _) (by norm_num)

end SevenEighths.ProbeFiniteProductBounds

end

end OAI
