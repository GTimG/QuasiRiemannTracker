/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact allocation polynomial expressed in literal child Inputs and pulled modifiers. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstChild
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstWindow
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput Record1252270103Source CenteredMomentSourceRow
open CenteredMomentGaussEnergy CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentLiveDomain
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance coupledFirstChildPolynomialDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma allocated_columns_child (s:Input ι)(C R seed L:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ) :
    (allocatedData (original s R seed) C L B).columns=
      finiteColumns (Fintype.piFinset (child s C R B τ t).pools) := by
  exact (child_columns s C R L B τ t).1

def childPolynomial (s:Input ι)(modifier:Tuple ι→ℂ)(C R L:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(t T:ℝ)(z:O):ℂ :=
  let s' := child s C R B τ t
  let S := finiteColumns (Fintype.piFinset s'.pools)
  gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
    (fun I:supportedColumns S=>(Real.sqrt T:ℂ)⁻¹*
      (coefficient s' (pulledModifier B.val modifier) (R*C) L I*rowWeight τ fixedBadMask 1 1 t I)) z

theorem allocated_modified_gauss_child (s:Input ι)(modifier:Tuple ι→ℂ)(C R seed L:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(t T:ℝ)(z:O) :
    gaussPolynomial Finset.univ (sourceGenerator (allocatedData (original s R seed) C L B).columns)
      (sourceGenerator_supported (allocatedData (original s R seed) C L B).columns)
      (modifiedRowCoefficient (allocatedData (original s R seed) C L B)
        (pulledModifier B.val modifier) τ fixedBadMask t T) z=
      childPolynomial s modifier C R L B τ t T z := by
  let f (S:Finset (Ideal O)) (β:Ideal O→ℂ):ℂ :=
    gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I:supportedColumns S=>(Real.sqrt T:ℂ)⁻¹*(β I*rowWeight τ fixedBadMask 1 1 t I)) z
  exact congrArg₂ f (allocated_columns_child s C R seed L B τ t)
    (allocated_modifiedBeta_child s modifier C R seed L B τ t)

theorem allocatedPolynomial_child (s:Input ι)(modifier:Tuple ι→ℂ)(C R seed L:Ideal O)
    (τ:Character)(t T:ℝ)(z:O) :
    allocatedPolynomial (original s R seed) modifier C L τ t T z=
      ∑B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P*
        childPolynomial s modifier C R L B τ t T z := by
  unfold allocatedPolynomial
  apply Finset.sum_congr rfl
  intro B hB
  exact congrArg (fun x:ℂ=>frozenCoefficient B.val C R s.ν s.W s.P*x)
    (allocated_modified_gauss_child s modifier C R seed L B τ t T z)

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.allocated_columns_child
#print axioms QRH.Record1252270103Source.High.CoupledFirst.allocated_modified_gauss_child
#print axioms QRH.Record1252270103Source.High.CoupledFirst.allocatedPolynomial_child
