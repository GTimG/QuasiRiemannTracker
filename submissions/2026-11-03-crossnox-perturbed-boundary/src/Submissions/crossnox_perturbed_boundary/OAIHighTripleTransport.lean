/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighTripleTransport.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighZTransport

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

theorem continued_triple_x_shift_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) < a) (ha3 : a ≤ 3)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 1 / 6 < ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
      LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z =>
      verticalIntegral 3 (fun w => F s w z))) =
    verticalIntegral 3 (fun s => verticalIntegral ξ (fun z =>
      verticalIntegral 3 (fun w => F s w z))) := by
  norm_num [boundary] at ha
  let F := fun s w z =>
    continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
    LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
    LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := continued_source_joint_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ
    (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by norm_num)
  have hi3 := continued_source_joint_integrable_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3)
    (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z =>
    verticalIntegral 3 (fun w => F s w z))) = _
  rw [verticalIntegral_triple_reverse F a ξ 3 hiA,
    verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply verticalIntegral_congr_line
  intro u
  apply verticalIntegral_congr_line
  intro v
  exact continued_x_shift_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem continued_triple_z_shift_on_perturbed_region
    {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : (boundary : ℝ) ≤ a) (ha3 : a ≤ 3)
    (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 1 / 6 < ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
      LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z =>
      verticalIntegral 3 (fun w => F s w z))) =
    verticalIntegral a (fun s => verticalIntegral 2 (fun z =>
      verticalIntegral 3 (fun w => F s w z))) := by
  norm_num [boundary] at ha
  let F := fun s w z =>
    continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
    LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
    LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ, Kξ, hCξ, hKξ, hξi⟩ :=
    continued_source_slices_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a ξ 3 3 hX hY hZ ha hβ
      (by linarith) (by norm_num) (by norm_num)
      (by linarith) (by norm_num) 0
  obtain ⟨C2, K2, hC2, hK2, h2i⟩ :=
    continued_source_slices_on_perturbed_region
      η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a 2 3 3 hX hY hZ ha hβ
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z =>
    verticalIntegral 3 (fun w => F s w z))) = _
  apply verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [verticalIntegral_swap (fun z w => F ((a : ℂ) + t * I) w z)
      ξ 3 hiξ,
    verticalIntegral_swap (fun z w => F ((a : ℂ) + t * I) w z)
      2 3 hi2]
  apply verticalIntegral_congr_line
  intro u
  exact continued_z_shift_on_perturbed_region
    η S hS hTail J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

end SevenEighths.ProbePrincipalTransport

end

end OAI
