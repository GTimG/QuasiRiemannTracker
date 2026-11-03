/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighSourceContours.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighComplexSlotBounds
import Submissions.crossnox_perturbed_boundary.OAIHighSourceWZ

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductBounds

open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem source_w_boundary_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0 < a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0 < Y)
    (s z : ℂ) (hs : (boundary : ℝ) ≤ s.re)
    (hz : (33 / 200 : ℝ) ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1 < cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
      LFunction (fixedPrincipal M) w) (19 / 20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1
    M X Y Z hY (η.excludePrimes S hS.prime) s z hEta
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3 / 2) * slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_w_on_perturbed_boundary
      η S hTail J T b hT s z hs (by linarith)).continuousOn.mono
        (by intro w hw; change (9 / 10 : ℝ) < w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero, mul_one] using
      bound_combined_slots_with_complex_weight_on_perturbed_boundary
        η S hTail J T b hT s ((x : ℂ) + t * I) z s.re z.re
        ⟨hs, le_rfl⟩ (by simpa using hx.1) ⟨hz, le_rfl⟩

theorem source_z_boundary_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ)
    (hX : 0 < X) (hZ : 0 < Z)
    (s : ℂ) (hs : (boundary : ℝ) ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0 < e) (he' : e ≤ 2 / 3) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedPrincipal M) (6 * z)) (33 / 200) (1 / 6 + e) := by
  apply PrincipalMellinGrowth.source_z_boundary W0 W1 a0 b0 ha0 hW0
    M X Y Z hX hZ (η.excludePrimes S hS.prime) s hEta
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3 / 2) * slotBound J T b s.re (1 / 6 + e)) he he'
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_z_on_perturbed_boundary
      η S hTail J T b hT s 1 hs (by norm_num)).continuousOn.mono
        (by intro z hz; change (4 / 25 : ℝ) < z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero, mul_one] using
      bound_combined_slots_with_complex_weight_on_perturbed_boundary
        η S hTail J T b hT s 1 ((x : ℂ) + t * I) s.re (1 / 6 + e)
        ⟨hs, le_rfl⟩ (by norm_num) (by simpa using hx)

theorem source_w_shift_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0 < a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0 < Y)
    (s z : ℂ) (hs : (boundary : ℝ) ≤ s.re)
    (hz : (33 / 200 : ℝ) ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1 < cw) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral cw (fun w => K w z * LFunction (fixedPrincipal M) w) =
      verticalIntegral (19 / 20) (fun w => K w z * LFunction (fixedPrincipal M) w) +
        K 1 z * fixedPrincipalResidue M := by
  dsimp only
  apply PrincipalMellinResidues.source_w_shift (fixedPrincipal M) _ z hcw
  · exact (source_multiplier_differentiable_w_on_perturbed_boundary
      η S hS hTail J T b hT W0 W1 a1 b1 ha1 hW1 X Y Z hY s z hs
      (by linarith)).mono
        (by intro w hw; change (9 / 10 : ℝ) < w.re; linarith [hw.1])
  · exact source_w_boundary_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a1 b1 ha1 hW1
      M X Y Z hY s z hs hz hEta hcw

theorem source_residue_z_shift_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ)
    (hX : 0 < X) (hZ : 0 < Z)
    (s : ℂ) (hs : (boundary : ℝ) ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0 < e) (he' : e ≤ 2 / 3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral (1 / 6 + e)
        (fun z => K 1 z * LFunction (fixedPrincipal M) (6 * z)) =
      verticalIntegral (33 / 200)
        (fun z => K 1 z * LFunction (fixedPrincipal M) (6 * z)) +
        K 1 (1 / 6) * fixedPrincipalResidue M / 6 := by
  dsimp only
  apply PrincipalMellinResidues.source_residue_z_shift (fixedPrincipal M) _ he
  · exact (source_multiplier_differentiable_z_on_perturbed_boundary
      η S hS hTail J T b hT W0 W1 X Y Z hX hZ s 1 hs
      (by norm_num)).mono
        (by intro z hz; change (4 / 25 : ℝ) < z.re; linarith [hz.1])
  · exact source_z_boundary_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 ha0 hW0
      M X Y Z hX hZ s hs hEta he he'

end SevenEighths.ProbeFiniteProductBounds

end

end OAI
