/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalAnalytic/PhysicalPrincipal.lean
Original SHA-256: da985407600f95f2f9719d4e9c1558e43cddf3ba11516bec166539907e7a7b90
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalAnalytic.ContourTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical

namespace LW56e2.Transport.PhysicalAnalytic.PhysicalPrincipal
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds CanonicalQuadraticSieve
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours ProbePrincipalPhysical
local notation "Id" => Ideal HeckeFamily.O

theorem principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : Contours.transportBoundary<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
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
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact ContourTransport.source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2


end
end LW56e2.Transport.PhysicalAnalytic.PhysicalPrincipal
