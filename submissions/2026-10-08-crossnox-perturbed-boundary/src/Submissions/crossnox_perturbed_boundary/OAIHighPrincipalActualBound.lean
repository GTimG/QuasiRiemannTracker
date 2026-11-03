/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalActualBound.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalNormalizedIdentity
import Submissions.crossnox_perturbed_boundary.OAIHighGlobalCorrection

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open ProbePhysical PrincipalMellinResidues ActualEisensteinCubic CompletedGauss
variable {κ : Type*}

theorem sourceCorrection_differentiable_on_perturbed_boundary (η : Character)
    (E : Finset (Ideal HeckeFamily.O)) (hE : PerturbedCorrectionTail E) :
    DifferentiableOn ℂ (sourceCorrection η E)
      {s : ℂ | perturbedBoundary < s.re} := by
  change DifferentiableOn ℂ (fun s => globalClosedCorrection η E s 1 (1/6))
    {s : ℂ | (boundary : ℝ) < s.re}
  exact (global_closed_correction_analytic_x_on_perturbed_region η E hE 1 (1/6)
    (by norm_num) (by norm_num)).differentiableOn

theorem sourceCorrection_bound_on_perturbed_boundary (η : Character)
    (E : Finset (Ideal HeckeFamily.O)) (hE : PerturbedCorrectionTail E)
    (s : ℂ) (hs : perturbedBoundary < s.re) :
    ‖sourceCorrection η E s - 1‖ ≤ 1/2 := by
  exact bound_global_closed_correction_on_perturbed_region η E hE s 1 (1/6)
    (by simpa only [perturbedBoundary] using hs.le) (by norm_num) (by norm_num)

theorem exists_normalized_actual_source_bound_on_perturbed_boundary
    (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (hTail : PerturbedCorrectionTail E)
    (η : Character) {a : ℝ}
    (ha : perturbedBoundary < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) (lengthShift : ℝ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ)
      (T : κ → Finset PrimeIdeal) (w : κ → PrimeIdeal → ℝ)
      (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-perturbedBoundary) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
        slotProduct S T w (fun _ p => Ideal.absNorm p.val)
          (fun _ p => actualAPhase η (primaryGenerator p.val))
          (fun _ p => idealCoeff η p.val) ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (1/6+lengthShift) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z^(xBase-lengthShift/2 : ℝ)) Y Z
          (η.excludePrimes E hE.prime) ((a : ℂ)+t*I)
          (globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^(xBase-lengthShift/2 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) signalOffset Z‖ ≤
        D * Z^(a+signalOffset) * P^(-perturbedBoundary) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨C, hC, hrec⟩ :=
    HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes E hE.prime) a hβ
  let D := HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S
  refine ⟨D, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold D HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := sourceResidueIntegral_normalized_with_perturbed_lengths W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z lengthShift (by linarith)
    (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hsmallSource : 1440 * P ^ (-(7/8 : ℝ)) ≤ 1 := by
    apply le_trans _ hsmall
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    unfold perturbedBoundary
    norm_num
  have hslots : SlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmallSource, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
        (hcop j hj p hp), hmass⟩
  have hbnd := slotResidue_bound_of_reciprocal_bound_on_perturbed_boundary
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (sourceCorrection_differentiable_on_perturbed_boundary η E hTail)
    (sourceCorrection_bound_on_perturbed_boundary η E hTail)
    ha ha2 hβ hC (fun s hs => hrec s hs) S T w
    (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hslots hsmall hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact source_double_residue_integrable_with_perturbed_lengths W0 W1
      (∏ p ∈ E, p) (η.excludePrimes E hE.prime) a Y Z lengthShift (by linarith)
      (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val)
      (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end SevenEighths.PrincipalSignalComparison
end

end OAI
