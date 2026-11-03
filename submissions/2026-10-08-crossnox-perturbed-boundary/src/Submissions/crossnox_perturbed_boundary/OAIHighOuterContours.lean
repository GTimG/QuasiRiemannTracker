/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighOuterContours.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighResidueBounds

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

theorem source_ordered_outer_on_perturbed_region
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
    let K := fun s => sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral a (fun s => verticalIntegral (1 / 6 + e)
      (fun z => verticalIntegral cw
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1 / 6 + e)
      (fun z => verticalIntegral (19 / 20)
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) +
    R * verticalIntegral a (fun s => verticalIntegral (33 / 200)
      (fun z => K s 1 z * LFunction π (6 * z))) +
    R ^ 2 / 6 * verticalIntegral a (fun s => K s 1 (1 / 6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z
    (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  let R := HeckeReciprocal.regularizedL π 1
  let A := fun s => verticalIntegral (1 / 6 + e) (fun z =>
    verticalIntegral cw (fun w =>
      K s w z * LFunction π (6 * z) * LFunction π w))
  let B := fun s => verticalIntegral (1 / 6 + e) (fun z =>
    verticalIntegral (19 / 20) (fun w =>
      K s w z * LFunction π (6 * z) * LFunction π w))
  let D := fun s => R * verticalIntegral (33 / 200)
    (fun z => K s 1 z * LFunction π (6 * z))
  let E := fun s => R ^ 2 / 6 * K s 1 (1 / 6)
  have hA : Integrable (fun t : ℝ => A ((a : ℂ) + t * I)) :=
    source_iterated_integrable_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1 / 6 + e) cw cw hX hY hZ ha hβ
      (by linarith) hcw ⟨by linarith, le_rfl⟩
      (by linarith) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a : ℂ) + t * I)) :=
    source_iterated_integrable_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1 / 6 + e) (19 / 20) cw hX hY hZ ha hβ
      (by linarith) hcw ⟨le_rfl, by linarith⟩
      (by linarith) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a : ℂ) + t * I)) :=
    (residue_iterated_integrable_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33 / 200) hX hZ ha hβ le_rfl
      (by norm_num)).const_mul R
  have hp : ∀ᵐ t : ℝ,
      A ((a : ℂ) + t * I) = B ((a : ℂ) + t * I) +
        D ((a : ℂ) + t * I) + E ((a : ℂ) + t * I) :=
    source_ordered_ae_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e cw hX hY hZ ha hβ hcw he
  have hE : Integrable (fun t : ℝ => E ((a : ℂ) + t * I)) := by
    apply ((hA.sub hB).sub hD).congr
    filter_upwards [hp] with t ht
    change A ((a : ℂ) + t * I) - B ((a : ℂ) + t * I) -
      D ((a : ℂ) + t * I) = E ((a : ℂ) + t * I)
    rw [ht]
    ring
  have heq : verticalIntegral a A =
      verticalIntegral a (fun s => B s + D s + E s) := by
    unfold verticalIntegral
    congr 1
    exact integral_congr_ae hp
  rw [verticalIntegral_add a _ _ (hB.add hD) hE,
    verticalIntegral_add a _ _ hB hD] at heq
  change verticalIntegral a A = verticalIntegral a B +
    R * verticalIntegral a _ + R ^ 2 / 6 * verticalIntegral a _
  rw [heq]
  simp only [D, E, verticalIntegral, integral_const_mul]
  ring

theorem source_initial_ordered_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z =>
      verticalIntegral 3
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) =
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z =>
      verticalIntegral (19 / 20)
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) +
    R * verticalIntegral 3 (fun s => verticalIntegral (33 / 200)
      (fun z => K s 1 z * LFunction π (6 * z))) +
    R ^ 2 / 6 * verticalIntegral 3 (fun s => K s 1 (1 / 6)) := by
  simpa only [show (1 / 6 + 11 / 6 : ℝ) = 2 by norm_num] using
    source_ordered_outer_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z 3 (11 / 6) 3 hX hY hZ (by norm_num)
      (by linarith [HeckeZeroSupremum.beta_le_one])
      (by norm_num) (by norm_num)

end SevenEighths.ProbePrincipalContours

end

end OAI
