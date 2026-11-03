/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighResidueBounds.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighOrderedContours

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem bound_residue_arithmetic_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (X Z a ξ C : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (ha : (AsymmetricGeometry.boundary : ℝ) ≤ a)
    (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤
        C * (1 + |s.im| ^ 2))
    (q : ℝ × ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z
      ((a : ℂ) + q.1 * I) ((ξ : ℂ) + q.2 * I)‖ ≤
      residueAmplitude S J T b X Z a ξ C *
        jointHeight q.1 q.2 0 ^ 5 := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime)
      ((a : ℂ) + q.1 * I)‖ ≤ C * height q.1 ^ 2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := bound_combined_slots_with_complex_weight_on_perturbed_boundary
    η S hTail J T b hT ((a : ℂ) + q.1 * I) 1
    ((ξ : ℂ) + q.2 * I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := fixed_principal_z_bound (∏ P ∈ S, P) ξ ξ q.2
    ⟨hξ, le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1 / 2 - ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a + ξ - 1)).le
  have hHB := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (zBoxAmplitude_nonneg (∏ P ∈ S, P) ξ)
    (abs_nonneg (6 * ξ - 1))
  have hq1 := (height_pos q.1).le
  have hq2 := (height_pos q.2).le
  have hqJ := (jointHeight_pos q.1 q.2 0).le
  calc
    _ = X ^ (1 / 2 - ξ) * Z ^ (a + ξ - 1) *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime)
          ((a : ℂ) + q.1 * I)‖ *
        ‖globalClosedCorrection η S ((a : ℂ) + q.1 * I) 1
          ((ξ : ℂ) + q.2 * I) *
          slotMultiplier η J T b ((a : ℂ) + q.1 * I) 1
            ((ξ : ℂ) + q.2 * I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + q.2 * I))‖ := by
      simp only [residueArithmetic, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.norm_cpow_eq_rpow_re_of_pos hZ]
      norm_num
    _ ≤ X ^ (1 / 2 - ξ) * Z ^ (a + ξ - 1) *
        (C * height q.1 ^ 2) * ((3 / 2) * slotBound J T b a ξ) *
        ((zBoxAmplitude (∏ P ∈ S, P) ξ / |6 * ξ - 1|) *
          height q.2 ^ 3) := by
      gcongr
      first | positivity | exact hL
    _ ≤ X ^ (1 / 2 - ξ) * Z ^ (a + ξ - 1) *
        (C * jointHeight q.1 q.2 0 ^ 2) *
        ((3 / 2) * slotBound J T b a ξ) *
        ((zBoxAmplitude (∏ P ∈ S, P) ξ / |6 * ξ - 1|) *
          jointHeight q.1 q.2 0 ^ 3) := by
      gcongr <;> first
        | positivity
        | exact height_le_joint_s _ _ _
        | exact height_le_joint_z _ _ _
    _ = _ := by
      unfold residueAmplitude
      ring

theorem continued_residue_pair_integrable_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (ha : (AsymmetricGeometry.boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1) :
    Integrable (fun q : ℝ × ℝ =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a : ℂ) + q.1 * I) 1 ((ξ : ℂ) + q.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((ξ : ℂ) + q.2 * I))) (volume.prod volume) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K, hK, hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a a ξ ξ 1 1 (by linarith) 5 0
  have hm := residue_arithmetic_measurable η S hS.prime J T b X Z a ξ
    hX hZ hβ (by linarith) hξ1
  have hb := bound_residue_arithmetic_on_perturbed_region
    η S hS hTail J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl, le_rfl⟩ ξ ⟨le_rfl, le_rfl⟩
    1 ⟨le_rfl, le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (residueAmplitude_nonneg S hS.prime J T b X Z a ξ C
      hX.le hZ.le hC)
    (fun q : ℝ × ℝ => residueArithmetic η S hS.prime J T b X Z
      ((a : ℂ) + q.1 * I) ((ξ : ℂ) + q.2 * I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap, onLines, ofReal_one, ofReal_zero,
    zero_mul, add_zero] using
      residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z
        ((a : ℂ) + q.1 * I) ((ξ : ℂ) + q.2 * I)

theorem residue_pair_integrable_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (ha : (AsymmetricGeometry.boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1) :
    Integrable (fun q : ℝ × ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a : ℂ) + q.1 * I)
        (globalClosedCorrection η S ((a : ℂ) + q.1 * I))
        (slotMultiplier η J T b ((a : ℂ) + q.1 * I))
        1 ((ξ : ℂ) + q.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((ξ : ℂ) + q.2 * I))) (volume.prod volume) := by
  apply (continued_residue_pair_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐ q : ℝ × ℝ ∂volume.prod volume, q.1 ≠ 0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0 : ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a : ℂ) + q.1 * I ≠ 0 := by
    intro h
    exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a : ℂ) + q.1 * I ≠ 1 := by
    intro h
    exact hq (by simpa using congrArg Complex.im h)
  rw [continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z
    _ _ _ h0 h1]

theorem source_iterated_integrable_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (AsymmetricGeometry.boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw)
    (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      verticalIntegral υ (fun w =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
          ((a : ℂ) + t * I)
          (globalClosedCorrection η S ((a : ℂ) + t * I))
          (slotMultiplier η J T b ((a : ℂ) + t * I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
        LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hi := source_joint_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral, integral_const_mul, mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul
      (((1 / (2 * Real.pi) : ℝ) : ℂ))).const_mul
        (((1 / (2 * Real.pi) : ℝ) : ℂ))

theorem residue_iterated_integrable_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (ha : (AsymmetricGeometry.boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a : ℂ) + t * I)
        (globalClosedCorrection η S ((a : ℂ) + t * I))
        (slotMultiplier η J T b ((a : ℂ) + t * I)) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z))) := by
  have hi := residue_pair_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using
    hi.integral_prod_left.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

end SevenEighths.ProbePrincipalContours

end

end OAI
