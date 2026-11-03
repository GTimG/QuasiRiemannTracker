/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighInitialPlacement.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighTripleTransport

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

theorem source_initial_placement_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) < a) (ha3 : a ≤ 3)
    (hβ : HeckeZeroSupremum.beta < a)
    (he : 0 < e) (he2 : e ≤ 11 / 6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z =>
      verticalIntegral 3
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1 / 6 + e)
      (fun z => verticalIntegral 3
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) := by
  norm_num [boundary] at ha
  dsimp only
  rw [← continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ← continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z
      a (1 / 6 + e) 3]
  have hx := continued_triple_x_shift_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := continued_triple_z_shift_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1 / 6 + e) hX hY hZ ha.le ha3 hβ
    (by linarith) (by linarith)
  exact hx.symm.trans hz.symm

theorem source_initial_ordered_at_a_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) < a) (ha3 : a ≤ 3)
    (hβ : HeckeZeroSupremum.beta < a)
    (he : 0 < e) (he2 : e ≤ 11 / 6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z
      (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z =>
      verticalIntegral 3
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1 / 6 + e)
      (fun z => verticalIntegral (19 / 20)
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) +
    R * verticalIntegral a (fun s => verticalIntegral (33 / 200)
      (fun z => K s 1 z * LFunction π (6 * z))) +
    R ^ 2 / 6 * verticalIntegral a (fun s => K s 1 (1 / 6)) := by
  exact (source_initial_placement_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
      (source_ordered_outer_on_perturbed_region
        η S hS hTail J T b hT W0 W1 a0 b0 a1 b1
        ha0 ha1 hW0 hW1 X Y Z a e 3 hX hY hZ
        ha.le hβ (by norm_num) he)

end SevenEighths.ProbePrincipalTransport

end

end OAI
