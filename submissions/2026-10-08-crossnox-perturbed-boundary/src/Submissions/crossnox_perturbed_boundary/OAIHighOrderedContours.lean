/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighOrderedContours.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighArithmeticLines
import Submissions.crossnox_perturbed_boundary.OAIHighSourceContours

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

theorem source_ordered_at_height_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hcw : 1 < cw) (he : 0 < e)
    (hs1 : (a : ℂ) + t * I ≠ 1) :
    let s : ℂ := (a : ℂ) + t * I
    let K := sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1 / 6 + e) (fun z => verticalIntegral cw
      (fun w => K w z * LFunction π (6 * z) * LFunction π w)) =
    verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
      (fun w => K w z * LFunction π (6 * z) * LFunction π w)) +
    HeckeReciprocal.regularizedL π 1 *
      verticalIntegral (33 / 200) (fun z => K 1 z * LFunction π (6 * z)) +
    (HeckeReciprocal.regularizedL π 1) ^ 2 / 6 * K 1 (1 / 6) := by
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (boundary : ℝ) ≤
      (((a : ℂ) + t * I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt
    (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta < (((a : ℂ) + t * I) : ℂ).re by
      simpa using hβ) (Or.inl hs1)
  have hzb := source_z_boundary_any_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a : ℂ) + t * I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (source_multiplier_differentiable_w_on_perturbed_boundary
      η S hS hTail J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a : ℂ) + t * I) z hs
      (by rw [hz]; linarith)).mono
    intro w hw
    change (9 / 10 : ℝ) < w.re
    linarith [hw.1]
  · intro z hz
    have hh := source_w_boundary_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY ((a : ℂ) + t * I) z hs
      (by rw [hz]; linarith) hη hcw
    convert boundary_mul_const _ _ _ hh
      (LFunction (fixedSourcePrincipal S hS.prime) (6 * z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal, fixedPrincipal]
    ring
  · apply (source_multiplier_differentiable_z_on_perturbed_boundary
      η S hS hTail J T b hT W0 W1 X Y Z hX hZ
      ((a : ℂ) + t * I) 1 hs (by norm_num)).mono
    intro z hz
    change (4 / 25 : ℝ) < z.re
    linarith [hz.1]
  · exact hzb
  · exact source_w_leftover_outer_integrable_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1
      ha0 ha1 hW0 hW1 X Y Z a e t hX hY hZ ha hβ he hs1

theorem source_ordered_ae_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hcw : 1 < cw) (he : 0 < e) :
    ∀ᵐ t : ℝ,
      let s : ℂ := (a : ℂ) + t * I
      let K := sourceMultiplier W0 W1 X Y Z
        (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s)
      let π := fixedSourcePrincipal S hS.prime
      verticalIntegral (1 / 6 + e) (fun z => verticalIntegral cw
        (fun w => K w z * LFunction π (6 * z) * LFunction π w)) =
      verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
        (fun w => K w z * LFunction π (6 * z) * LFunction π w)) +
      HeckeReciprocal.regularizedL π 1 *
        verticalIntegral (33 / 200) (fun z => K 1 z * LFunction π (6 * z)) +
      (HeckeReciprocal.regularizedL π 1) ^ 2 / 6 * K 1 (1 / 6) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply source_ordered_at_height_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

end SevenEighths.ProbePrincipalContours

end

end OAI
