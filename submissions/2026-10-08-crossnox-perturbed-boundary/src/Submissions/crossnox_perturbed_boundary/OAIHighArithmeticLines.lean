/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighArithmeticLines.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighComplexSlotBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalContours

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem bound_arithmetic_on_lines_with_gaps_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) ≤ a)
    (hσ : σ ∈ Icc a Bs) (hξ : ξ ∈ Icc (33 / 200 : ℝ) Bz)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw)
    (δw δz : ℝ) (hdw : 0 < δw) (hdz : 0 < δz)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤
        C * (1 + |s.im| ^ 2))
    (p : HeightSpace)
    (hwgap : δw ≤ ‖((υ : ℂ) + p.2 * I) - 1‖)
    (hzgap : δz ≤ ‖6 * ((ξ : ℂ) + p.1.2 * I) - 1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I)
      ((ξ : ℂ) + p.1.2 * I)‖ ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2 ^ 8 := by
  norm_num [boundary] at ha
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hx := cpow_le_scaleBound hX (1 / 2 - ((ξ : ℂ) + p.1.2 * I))
    (show (1 / 2 - ((ξ : ℂ) + p.1.2 * I) : ℂ).re ∈
      Icc (1 / 2 - Bz) (1 / 2 - 33 / 200) by
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re,
        I_im, mul_zero, zero_mul, sub_self, add_zero]
      norm_num only [show (1 / 2 : ℂ).re = 1 / 2 by norm_num]
      constructor <;> linarith [hξ.1, hξ.2])
  have hz := cpow_le_scaleBound hZ
    (((σ : ℂ) + p.1.1 * I) + ((ξ : ℂ) + p.1.2 * I) - 1)
    (show ((((σ : ℂ) + p.1.1 * I) + ((ξ : ℂ) + p.1.2 * I) - 1) : ℂ).re ∈
      Icc (a + 33 / 200 - 1) (Bs + Bz - 1) by
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re,
        I_im, mul_zero, zero_mul, sub_self, add_zero, one_re]
      constructor <;> linarith [hσ.1, hσ.2, hξ.1, hξ.2])
  have hy := cpow_le_scaleBound hY (((υ : ℂ) + p.2 * I) - 1)
    (show (((υ : ℂ) + p.2 * I) - 1 : ℂ).re ∈ Icc (19 / 20 - 1) (cw - 1) by
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re,
        I_im, mul_zero, zero_mul, sub_self, add_zero, one_re]
      constructor <;> linarith [hυ.1, hυ.2])
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime)
      ((σ : ℂ) + p.1.1 * I)‖ ≤ C * height p.1.1 ^ 2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := bound_combined_slots_with_complex_weight_on_perturbed_boundary
    η S hTail J T b hT ((σ : ℂ) + p.1.1 * I)
    ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) Bs Bz
    (by simpa using And.intro (ha.trans hσ.1) hσ.2)
    (by simpa using hυ.1) (by simpa using hξ)
  have hw0 : (υ : ℂ) + p.2 * I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith [hυ.1]
  have hw1 : (υ : ℂ) + p.2 * I ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hwgap
    linarith
  have hz0 : (6 * ((ξ : ℂ) + p.1.2 * I) : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith [hξ.1]
  have hz1 : (6 * ((ξ : ℂ) + p.1.2 * I) : ℂ) ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hzgap
    linarith
  have hlz0 := LFunction_norm_le_of_poleRemoved
    (fixedPrincipal (∏ P ∈ S, P)) _ hz0 hz1 _ _ hdz hzgap
    (fixed_principal_z_box_growth (∏ P ∈ S, P) Bz ξ p.1.2 hξ)
  have hlw0 := LFunction_norm_le_of_poleRemoved
    (fixedPrincipal (∏ P ∈ S, P)) _ hw0 hw1 _ _ hdw hwgap
    (fixed_principal_w_growth (∏ P ∈ S, P) hcw hυ p.2)
  have hlz : ‖LFunction (fixedPrincipal (∏ P ∈ S, P))
      (6 * ((ξ : ℂ) + p.1.2 * I))‖ ≤
      (zBoxAmplitude (∏ P ∈ S, P) Bz / δz) * height p.1.2 ^ 3 := by
    convert hlz0 using 1
    ring
  have hlw : ‖LFunction (fixedPrincipal (∏ P ∈ S, P))
      ((υ : ℂ) + p.2 * I)‖ ≤
      (wAmplitude (∏ P ∈ S, P) cw / δw) * height p.2 ^ 3 := by
    convert hlw0 using 1
    ring
  have hp1 := (height_pos p.1.1).le
  have hp2 := (height_pos p.1.2).le
  have hp3 := (height_pos p.2).le
  have hpJ := (jointHeight_pos p.1.1 p.1.2 p.2).le
  have hsX := (scaleBound_pos X (1 / 2 - Bz) (1 / 2 - 33 / 200)).le
  have hsY := (scaleBound_pos Y (19 / 20 - 1) (cw - 1)).le
  have hsZ := (scaleBound_pos Z (a + 33 / 200 - 1) (Bs + Bz - 1)).le
  have hHB := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏ P ∈ S, P) Bz) hdz.le
  have hAW := div_nonneg (wAmplitude_pos (∏ P ∈ S, P) hcw).le hdw.le
  calc
    _ = ‖(X : ℂ) ^ (1 / 2 - ((ξ : ℂ) + p.1.2 * I))‖ *
        ‖(Z : ℂ) ^ (((σ : ℂ) + p.1.1 * I) + ((ξ : ℂ) + p.1.2 * I) - 1)‖ *
        ‖(Y : ℂ) ^ (((υ : ℂ) + p.2 * I) - 1)‖ *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime)
          ((σ : ℂ) + p.1.1 * I)‖ *
        ‖globalClosedCorrection η S ((σ : ℂ) + p.1.1 * I)
          ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
          slotMultiplier η J T b ((σ : ℂ) + p.1.1 * I)
            ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + p.1.2 * I))‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime)
          ((υ : ℂ) + p.2 * I)‖ := by
      simp only [arithmeticMultiplier, norm_mul]
    _ ≤ scaleBound X (1 / 2 - Bz) (1 / 2 - 33 / 200) *
        scaleBound Z (a + 33 / 200 - 1) (Bs + Bz - 1) *
        scaleBound Y (19 / 20 - 1) (cw - 1) *
        (C * height p.1.1 ^ 2) *
        ((3 / 2) * slotBound J T b Bs Bz) *
        ((zBoxAmplitude (∏ P ∈ S, P) Bz / δz) * height p.1.2 ^ 3) *
        ((wAmplitude (∏ P ∈ S, P) cw / δw) * height p.2 ^ 3) := by
      gcongr <;> first | positivity | exact hlz | exact hlw
    _ ≤ scaleBound X (1 / 2 - Bz) (1 / 2 - 33 / 200) *
        scaleBound Z (a + 33 / 200 - 1) (Bs + Bz - 1) *
        scaleBound Y (19 / 20 - 1) (cw - 1) *
        (C * jointHeight p.1.1 p.1.2 p.2 ^ 2) *
        ((3 / 2) * slotBound J T b Bs Bz) *
        ((zBoxAmplitude (∏ P ∈ S, P) Bz / δz) *
          jointHeight p.1.1 p.1.2 p.2 ^ 3) *
        ((wAmplitude (∏ P ∈ S, P) cw / δw) *
          jointHeight p.1.1 p.1.2 p.2 ^ 3) := by
      gcongr <;> first
        | positivity
        | exact height_le_joint_s _ _ _
        | exact height_le_joint_z _ _ _
        | exact height_le_joint_w _ _ _
    _ = _ := by
      unfold arithmeticAmplitude boxScale
      ring

theorem bound_arithmetic_on_lines_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) ≤ a)
    (hσ : σ ∈ Icc a Bs) (hξ : ξ ∈ Icc (33 / 200 : ℝ) Bz)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw)
    (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤
        C * (1 + |s.im| ^ 2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I)
      ((ξ : ℂ) + p.1.2 * I)‖ ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C
        |υ - 1| |6 * ξ - 1| * jointHeight p.1.1 p.1.2 p.2 ^ 8 := by
  apply bound_arithmetic_on_lines_with_gaps_on_perturbed_region
    η S hS hTail J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ - 1| |6 * ξ - 1|
    (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6 * ((ξ : ℂ) + p.1.2 * I) - 1)

theorem continued_source_joint_integrable_on_perturbed_region
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
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw)
    (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I)
        ((ξ : ℂ) + p.1.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((ξ : ℂ) + p.1.2 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime)
        ((υ : ℂ) + p.2 * I)) heightMeasure := by
  norm_num [boundary] at ha
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ υ (by linarith)
    (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I)
      ((ξ : ℂ) + p.1.2 * I))
    (arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ
      hX hY hZ hβ (by linarith) hξ1 (by linarith [hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C
      |υ - 1| |6 * ξ - 1|) 8
    (bound_arithmetic_on_lines_on_perturbed_region
      η S hS hTail J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl, le_rfl⟩ ⟨hξ, le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall
    (fun p => arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

theorem source_joint_integrable_on_perturbed_region
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
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw)
    (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a : ℂ) + p.1.1 * I)
        (globalClosedCorrection η S ((a : ℂ) + p.1.1 * I))
        (slotMultiplier η J T b ((a : ℂ) + p.1.1 * I))
        ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((ξ : ℂ) + p.1.2 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime)
        ((υ : ℂ) + p.2 * I)) heightMeasure := by
  apply (continued_source_joint_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [continued_joint_ae_raw η S hS.prime J T b
    W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem source_joint_fubini_on_perturbed_region
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
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw)
    (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) :
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a : ℂ) + p.1.1 * I)
        (globalClosedCorrection η S ((a : ℂ) + p.1.1 * I))
        (slotMultiplier η J T b ((a : ℂ) + p.1.1 * I))
        ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((ξ : ℂ) + p.1.2 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime)
        ((υ : ℂ) + p.2 * I)
    ((∫ p, F p ∂heightMeasure) = ∫ t : ℝ, ∫ v : ℝ,
      ∫ u : ℝ, F ((t, v), u)) ∧
    ((∫ p, F p ∂heightMeasure) = ∫ u : ℝ, ∫ v : ℝ,
      ∫ t : ℝ, F ((t, v), u)) := by
  dsimp only
  have hi := source_joint_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu

theorem continued_source_slices_on_perturbed_region
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
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw)
    (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) (N : ℕ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧ ∀ axis : SliceAxis, ∀ R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
          ((a : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I)
          ((ξ : ℂ) + p.1.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + p.1.2 * I)) *
        LFunction (fixedSourcePrincipal S hS.prime)
          ((υ : ℂ) + p.2 * I)
      Integrable (fun q : ℝ × ℝ => F (sliceMap axis R q))
        (volume.prod volume) ∧
      (∫ q : ℝ × ℝ, ‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C
          |υ - 1| |6 * ξ - 1| * K / height R ^ N := by
  norm_num [boundary] at ha
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K, hK, hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C, K, hC, hK, ?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p =>
    arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I)
      ((ξ : ℂ) + p.1.2 * I)
  have hm := arithmetic_onLines_measurable η S hS.prime J T b
    X Y Z a ξ υ hX hY hZ hβ (by linarith) hξ1
    (by linarith [hυ.1]) hυ1
  have hbound := bound_arithmetic_on_lines_on_perturbed_region
    η S hS hTail J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl, le_rfl⟩ ⟨hξ, le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl, le_rfl⟩ ξ ⟨le_rfl, le_rfl⟩
    υ ⟨le_rfl, le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C
      |υ - 1| |6 * ξ - 1|)
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C
      _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q))
    ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G, onLines, arithmetic_profile_eq_source] using hh

theorem source_w_leftover_outer_integrable_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a) (he : 0 < e)
    (hs1 : (a : ℂ) + t * I ≠ 1) :
    let s : ℂ := (a : ℂ) + t * I
    let K := sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19 / 20) (fun w =>
      K w ((1 / 6 + e : ℝ) + v * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((1 / 6 + e : ℝ) + v * I)) *
      LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  norm_num [boundary] at ha
  obtain ⟨C, K, hC, hK, hslice⟩ :=
    continued_source_slices_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1
      ha0 ha1 hW0 hW1 X Y Z a (1 / 6 + e) (19 / 20) 3
      hX hY hZ ha hβ (by linarith) (by norm_num) (by norm_num)
      (by linarith) (by norm_num) 0
  have hi := (hslice .s t).1
  have hs0 : (a : ℂ) + t * I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hpair : Integrable (fun q : ℝ × ℝ =>
      sourceMultiplier W0 W1 X Y Z
        (η.excludePrimes S hS.prime) ((a : ℂ) + t * I)
        (globalClosedCorrection η S ((a : ℂ) + t * I))
        (slotMultiplier η J T b ((a : ℂ) + t * I))
        ((19 / 20 : ℝ) + q.2 * I) ((1 / 6 + e : ℝ) + q.1 * I) *
      LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((1 / 6 + e : ℝ) + q.1 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime)
        ((19 / 20 : ℝ) + q.2 * I)) (volume.prod volume) := by
    simpa only [sliceMap, continued_source_eq_raw η S hS.prime J T b
      W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using
    hpair.integral_prod_left.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

theorem source_z_boundary_any_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (X Y Z : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (s : ℂ) (hs : (boundary : ℝ) ≤ s.re)
    (hη : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0 < e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z))
      (33 / 200) (1 / 6 + e) := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0
    (∏ P ∈ S, P) X Y Z hX hZ (η.excludePrimes S hS.prime)
    s hη (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3 / 2) * slotBound J T b s.re (1 / 6 + e))
    (AL := zBoxAmplitude (∏ P ∈ S, P) (1 / 6 + e))
    he (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _))
    (zBoxAmplitude_nonneg _ _) 0 3
  · exact (combined_slot_analytic_z_on_perturbed_boundary
      η S hTail J T b hT s 1 hs (by norm_num)).continuousOn.mono
        (by intro z hz; change (4 / 25 : ℝ) < z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero, mul_one] using
      bound_combined_slots_with_complex_weight_on_perturbed_boundary
        η S hTail J T b hT s 1 ((x : ℂ) + t * I)
        s.re (1 / 6 + e) ⟨hs, le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact fixed_principal_z_box_growth (∏ P ∈ S, P) (1 / 6 + e) x t hx

end SevenEighths.ProbePrincipalContours

end

end OAI
