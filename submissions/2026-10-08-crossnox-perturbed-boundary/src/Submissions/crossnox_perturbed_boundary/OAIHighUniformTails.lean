/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighUniformTails.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighOuterContours

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours
open AsymmetricGeometry

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem source_uniform_joint_tails_on_perturbed_region
    {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (a Bs Bz cw : ℝ)
    (ha : boundary ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hcw : 1 < cw) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (η : Character) (S : Finset Id)
      (hS : SourceExclusions S), PerturbedCorrectionTail S →
      ∀ (J : Finset ι) (T : ι → Finset PrimeIdeal)
      (b : ι → PrimeIdeal → ℂ),
      (∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) →
      ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ Icc a Bs, ∀ ξ ∈ Icc (33 / 200 : ℝ) Bz,
      ∀ υ ∈ Icc (19 / 20 : ℝ) cw,
      6 * ξ ≠ 1 → υ ≠ 1 → ∀ R : ℝ, 0 ≤ R →
      (∫ p : HeightSpace in outsideBox R,
        ‖sourceMultiplier W0 W1 X Y Z
          (η.excludePrimes S hS.prime) ((σ : ℂ) + p.1.1 * I)
          (globalClosedCorrection η S ((σ : ℂ) + p.1.1 * I))
          (slotMultiplier η J T b ((σ : ℂ) + p.1.1 * I))
          ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
          LFunction (fixedSourcePrincipal S hS.prime)
            (6 * ((ξ : ℂ) + p.1.2 * I)) *
          LFunction (fixedSourcePrincipal S hS.prime)
            ((υ : ℂ) + p.2 * I)‖ ∂heightMeasure) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C
        |υ - 1| |6 * ξ - 1| * K / (1 + R) ^ N := by
  obtain ⟨K, hK, hk⟩ := profile_uniform_tails
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33 / 200) Bz (19 / 20) cw (by norm_num) 8 N
  obtain ⟨K0, hK0, hm⟩ := profile_uniform_moments
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33 / 200) Bz (19 / 20) cw (by norm_num) 8
  refine ⟨K, hK, ?_⟩
  intro η S hS hTail J T b hT X Y Z hX hY hZ
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  refine ⟨C, hC, ?_⟩
  intro σ hσ ξ hξ υ hυ hξ1 hυ1 R hR0
  let A := arithmeticAmplitude S J T b X Y Z a Bs Bz cw C
    |υ - 1| |6 * ξ - 1|
  have hA : 0 ≤ A := arithmeticAmplitude_nonneg
    S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
    (abs_nonneg _) (abs_nonneg _)
  have hi := source_joint_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z σ ξ υ cw hX hY hZ (ha.trans hσ.1)
    (hβ.trans_le hσ.1) hξ.1 hcw hυ hξ1 hυ1
  have hmi := (hm σ hσ ξ hξ υ hυ).1
  have hbound := bound_arithmetic_on_lines_on_perturbed_region
    η S hS hTail J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ hξ1 hυ1 hC hR
  have hdom : ∀ᵐ p : HeightSpace ∂heightMeasure,
      ‖sourceMultiplier W0 W1 X Y Z
        (η.excludePrimes S hS.prime) ((σ : ℂ) + p.1.1 * I)
        (globalClosedCorrection η S ((σ : ℂ) + p.1.1 * I))
        (slotMultiplier η J T b ((σ : ℂ) + p.1.1 * I))
        ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + p.1.2 * I)) *
        LFunction (fixedSourcePrincipal S hS.prime)
          ((υ : ℂ) + p.2 * I)‖ ≤
      A * (jointHeight p.1.1 p.1.2 p.2 ^ 8 *
        ‖onLines W0 W1 σ ξ υ p‖) := by
    filter_upwards [continued_joint_ae_raw η S hS.prime J T b
      W0 W1 X Y Z σ ξ υ] with p hp
    rw [← hp, ← arithmetic_profile_eq_source]
    rw [norm_mul]
    simpa only [mul_assoc, A, onLines] using
      mul_le_mul_of_nonneg_right (hbound p)
        (norm_nonneg (onLines W0 W1 σ ξ υ p))
  calc
    _ ≤ ∫ p : HeightSpace in outsideBox R,
        A * (jointHeight p.1.1 p.1.2 p.2 ^ 8 *
          ‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure :=
      integral_mono_ae hi.norm.integrableOn
        (hmi.const_mul A).integrableOn (ae_restrict_of_ae hdom)
    _ = A * (∫ p : HeightSpace in outsideBox R,
        jointHeight p.1.1 p.1.2 p.2 ^ 8 *
          ‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) :=
      integral_const_mul _ _
    _ ≤ A * (K / (1 + R) ^ N) :=
      mul_le_mul_of_nonneg_left (hk σ hσ ξ hξ υ hυ R hR0) hA
    _ = _ := by dsimp [A]; ring

end SevenEighths.ProbePrincipalContours

end

end OAI
