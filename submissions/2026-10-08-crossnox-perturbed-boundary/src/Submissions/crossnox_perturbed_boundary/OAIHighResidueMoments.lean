/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighResidueMoments.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighHighSlices

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem residue_uniform_moments_on_perturbed_region
    {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (a ξ : ℝ)
    (ha : (AsymmetricGeometry.boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (η : Character) (S : Finset Id)
      (hS : SourceExclusions S), PerturbedCorrectionTail S →
      ∀ (J : Finset ι) (T : ι → Finset PrimeIdeal)
      (b : ι → PrimeIdeal → ℂ),
      (∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) →
      ∀ X Y Z : ℝ, 0 < X → 0 < Z →
      ∃ C : ℝ, 0 ≤ C ∧
      let F := fun q : ℝ × ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
          ((a : ℂ) + q.1 * I)
          (globalClosedCorrection η S ((a : ℂ) + q.1 * I))
          (slotMultiplier η J T b ((a : ℂ) + q.1 * I))
          1 ((ξ : ℂ) + q.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + q.2 * I))
      Integrable (fun q : ℝ × ℝ =>
        jointHeight q.1 q.2 0 ^ N * ‖F q‖) (volume.prod volume) ∧
      (∫ q : ℝ × ℝ, jointHeight q.1 q.2 0 ^ N *
        ‖F q‖ ∂volume.prod volume) ≤
          residueAmplitude S J T b X Z a ξ C * K := by
  obtain ⟨K, hK, hk⟩ := profile_uniform_slices
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) (5 + N) 0
  refine ⟨K, hK, ?_⟩
  intro η S hS hTail J T b hT X Y Z hX hZ
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  refine ⟨C, hC, ?_⟩
  let A := residueAmplitude S J T b X Z a ξ C
  have hA : 0 ≤ A := residueAmplitude_nonneg
    S hS.prime J T b X Z a ξ C hX.le hZ.le hC
  let F : ℝ × ℝ → ℂ := fun q =>
    residueArithmetic η S hS.prime J T b X Z
      ((a : ℂ) + q.1 * I) ((ξ : ℂ) + q.2 * I) *
    onLines W0 W1 a ξ 1 (sliceMap .w 0 q)
  have hm := residue_arithmetic_measurable η S hS.prime J T b
    X Z a ξ hX hZ hβ (by linarith) hξ1
  have hFc : AEStronglyMeasurable F (volume.prod volume) :=
    hm.aestronglyMeasurable.mul
      (((onLines_continuous W0 W1 a1 b1 ha1 hW1 a ξ 1
        (by linarith)).comp (sliceMap_continuous .w 0)).aestronglyMeasurable)
  have hb := bound_residue_arithmetic_on_perturbed_region
    η S hS hTail J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hmom := hk a ⟨le_rfl, le_rfl⟩ ξ ⟨le_rfl, le_rfl⟩
    1 ⟨le_rfl, le_rfl⟩ .w 0
  have hdom (q : ℝ × ℝ) :
      jointHeight q.1 q.2 0 ^ N * ‖F q‖ ≤
        A * (jointHeight q.1 q.2 0 ^ (5 + N) *
          ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) := by
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ jointHeight q.1 q.2 0 ^ N *
          ((A * jointHeight q.1 q.2 0 ^ 5) *
            ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hb q) (norm_nonneg _))
          (pow_nonneg (jointHeight_pos _ _ _).le _)
      _ = _ := by rw [pow_add]; ring
  have hi : Integrable (fun q : ℝ × ℝ =>
      jointHeight q.1 q.2 0 ^ N * ‖F q‖) (volume.prod volume) := by
    apply (hmom.1.const_mul A).mono'
    · exact (by unfold jointHeight; fun_prop :
        Continuous (fun q : ℝ × ℝ =>
          jointHeight q.1 q.2 0 ^ N)).aestronglyMeasurable.mul hFc.norm
    · apply Eventually.of_forall
      intro q
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg
          (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)),
        sliceMap] using hdom q
  have hn : (∫ q : ℝ × ℝ,
      jointHeight q.1 q.2 0 ^ N * ‖F q‖ ∂volume.prod volume) ≤
      A * K := by
    calc
      _ ≤ ∫ q : ℝ × ℝ,
          A * (jointHeight q.1 q.2 0 ^ (5 + N) *
            ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖)
            ∂volume.prod volume :=
        integral_mono hi (hmom.1.const_mul A) hdom
      _ = A * (∫ q : ℝ × ℝ,
          jointHeight q.1 q.2 0 ^ (5 + N) *
            ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖
            ∂volume.prod volume) := integral_const_mul _ _
      _ ≤ A * K := mul_le_mul_of_nonneg_left
        (by simpa only [sliceMap, pow_zero, div_one] using hmom.2) hA
  have heq : F =ᵐ[volume.prod volume] (fun q : ℝ × ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a : ℂ) + q.1 * I)
        (globalClosedCorrection η S ((a : ℂ) + q.1 * I))
        (slotMultiplier η J T b ((a : ℂ) + q.1 * I))
        1 ((ξ : ℂ) + q.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((ξ : ℂ) + q.2 * I))) := by
    have hh : ∀ᵐ q : ℝ × ℝ ∂volume.prod volume, q.1 ≠ 0 :=
      Measure.quasiMeasurePreserving_fst.ae
        (Measure.ae_ne volume (0 : ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a : ℂ) + q.1 * I ≠ 0 := by
      intro h
      exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a : ℂ) + q.1 * I ≠ 1 := by
      intro h
      exact hq (by simpa using congrArg Complex.im h)
    dsimp only [F, onLines, sliceMap]
    simp only [ofReal_one, ofReal_zero, zero_mul, add_zero]
    rw [residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z,
      continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z
        _ _ _ h0 h1]
  have hweight : (fun q : ℝ × ℝ => jointHeight q.1 q.2 0 ^ N) =ᵐ[volume.prod volume]
      (fun q : ℝ × ℝ => jointHeight q.1 q.2 0 ^ N) :=
    Eventually.of_forall (fun _ => rfl)
  have heqw := hweight.mul (heq.fun_comp (fun z : ℂ => ‖z‖))
  exact ⟨hi.congr heqw, (integral_congr_ae heqw).symm.trans_le hn⟩

theorem residue_uniform_tails_on_perturbed_region
    {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (a ξ : ℝ)
    (ha : (AsymmetricGeometry.boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (η : Character) (S : Finset Id)
      (hS : SourceExclusions S), PerturbedCorrectionTail S →
      ∀ (J : Finset ι) (T : ι → Finset PrimeIdeal)
      (b : ι → PrimeIdeal → ℂ),
      (∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) →
      ∀ X Y Z : ℝ, 0 < X → 0 < Z →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      let F := fun q : ℝ × ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
          ((a : ℂ) + q.1 * I)
          (globalClosedCorrection η S ((a : ℂ) + q.1 * I))
          (slotMultiplier η J T b ((a : ℂ) + q.1 * I))
          1 ((ξ : ℂ) + q.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + q.2 * I))
      (∫ q : ℝ × ℝ in residueOutside R, ‖F q‖ ∂volume.prod volume) ≤
        residueAmplitude S J T b X Z a ξ C * K / (1 + R) ^ N := by
  obtain ⟨K, hK, hk⟩ := residue_uniform_moments_on_perturbed_region
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξ ha hβ hξ hξ1 N
  refine ⟨K, hK, ?_⟩
  intro η S hS hTail J T b hT X Y Z hX hZ
  obtain ⟨C, hC, hi, hb⟩ := hk η S hS hTail J T b hT X Y Z hX hZ
  refine ⟨C, hC, ?_⟩
  intro R hR
  let F := fun q : ℝ × ℝ =>
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a : ℂ) + q.1 * I)
      (globalClosedCorrection η S ((a : ℂ) + q.1 * I))
      (slotMultiplier η J T b ((a : ℂ) + q.1 * I))
      1 ((ξ : ℂ) + q.2 * I) *
    LFunction (fixedSourcePrincipal S hS.prime)
      (6 * ((ξ : ℂ) + q.2 * I))
  have hF := residue_pair_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  have hdom (q : ℝ × ℝ) (hq : q ∈ residueOutside R) :
      ‖F q‖ ≤ jointHeight q.1 q.2 0 ^ N * ‖F q‖ / (1 + R) ^ N := by
    have hh : 1 + R ≤ jointHeight q.1 q.2 0 := by
      rcases hq with h | h <;> unfold jointHeight <;>
        simp only [abs_zero, add_zero] <;>
        linarith [abs_nonneg q.1, abs_nonneg q.2]
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + R) hh N
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1 + R) N)).mpr
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hp (norm_nonneg (F q))
  change (∫ q : ℝ × ℝ in residueOutside R,
    ‖F q‖ ∂volume.prod volume) ≤ _
  calc
    _ ≤ ∫ q : ℝ × ℝ in residueOutside R,
        jointHeight q.1 q.2 0 ^ N * ‖F q‖ / (1 + R) ^ N
          ∂volume.prod volume :=
      setIntegral_mono_on hF.norm.integrableOn
        (hi.div_const _).integrableOn
        (residueOutside_measurable R) hdom
    _ = (∫ q : ℝ × ℝ in residueOutside R,
        jointHeight q.1 q.2 0 ^ N * ‖F q‖
          ∂volume.prod volume) / (1 + R) ^ N := integral_div _ _
    _ ≤ (∫ q : ℝ × ℝ,
        jointHeight q.1 q.2 0 ^ N * ‖F q‖
          ∂volume.prod volume) / (1 + R) ^ N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_le_integral hi
        (Eventually.of_forall (fun q =>
          mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _)
            (norm_nonneg _)))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

end SevenEighths.ProbePrincipalContours

end

end OAI
