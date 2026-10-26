/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual first MAIN correction is evaluated on the complete child column.
The extracted common ideal remains in the row puncture and frozen profiles. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.SelectedExceptionalInitialCapsFamily

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput
open Cycle61InitialMass RayFourExpansion Record1252270103Second
open Low.SelectedExceptionalNormalized Low.SelectedExceptionalInitialCaps
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
local instance mainFamilyDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

variable {α Label:Type*}[Fintype α][Fintype Label]
variable (s:Input α)(W W₁ W₂:𝓢(ℝ,ℂ))(Z:ℝ)(R:Ideal O)
    (C seed:Label→Ideal O)(B:∀l,actualAllocations s.pools (C l))
    (τ:Label→Character)(t:Label→ℝ)(P:Finset (Ideal O))
    (hseed:∀l,Squarefree (seed l))(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (K Tsec Tenergy amplitude:Label→ℝ)(ξ:ℝ)(hK:∀l,0<K l)
    (χ₀:Label→RayCharacter)(m:O)

def mainAllocatedFamily:CorrectedFamilyData (fun l=>liveIndices (B l).val) W Z :=
  { allocatedFamily s W W₁ W₂ Z R C seed B τ t P hseed hz₁ hz₂ K Tsec
      Tenergy amplitude ξ hK χ₀ m with
    frozen:=fun _=>1 }

theorem mainAllocatedFamily_modifier (l:Label):
    (mainAllocatedFamily s W W₁ W₂ Z R C seed B τ t P hseed hz₁ hz₂
      K Tsec Tenergy amplitude ξ hK χ₀ m).modifier l=
      markedSourceModifier ((B l).val (Sum.inr 0)) ((B l).val (Sum.inr 1)) 1
        (markedProduct (B l).val) (poolCorrection P) := rfl

end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.mainAllocatedFamily
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.mainAllocatedFamily_modifier
