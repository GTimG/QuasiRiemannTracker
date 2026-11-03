/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalPool.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighInitialPlacement
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalWindow
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem principal_physical_pool_ordered_on_perturbed_boundary {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : (boundary : ℝ)<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  have hinit := principal_physical_pool_initial η S hS T hT hdis b W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hi := source_joint_integrable η S hS Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by norm_num)
    (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htriple :=
    (ProbePrincipalRemainderBounds.vertical_triple_eq_joint
      (principalPoolKernel η S hS T b W0 W1 X Y Z) 3 2 3 hi).symm
  rw [hinit]
  exact htriple.trans (ProbePrincipalTransport.source_initial_ordered_at_a_on_perturbed_region η S hS hTail Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2)

end SevenEighths.ProbePrincipalPhysical
end

end OAI
