/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle62.Physical.InitialMass.GeometryMainCostReduction

set_option autoImplicit false
set_option maxHeartbeats 50000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance selectedCompleteCostSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The cost used to choose supported first allocations is exactly the
complete second-block cost on the selected family. Only the original full
nonzero filter occurs, and no number of labels or allocations is paid. -/
theorem actual_main_selected_complete_cost
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (mass : Label→ℝ) (χ : RayCharacter) (Q : Ideal O) (m : O)
    (a ap : ℝ) (second : Bool) (t₀ u : ℝ) :
    (∑l,mass l*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m a ap second t₀ u (firstIndex l))=
    ∑r : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key
        hz₁ hz₂ firstIndex,
      (mass r.val.1/volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t (firstIndex r.val.1)))*
      mainNormalizedBlockCost N a ap second
        (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m ⟨firstIndex r.val.1,r.val.2⟩) t₀ u := by
  let Child := fun l=>GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    (firstIndex l)
  let rows := mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ firstIndex
  let vol := fun l=>volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t (firstIndex l))
  let cost := fun r : Sigma Child=>mainNormalizedBlockCost N a ap second
    (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m ⟨firstIndex r.1,r.2⟩) t₀ u
  have hs := filtered_sigma_weighted_cost rows mass vol cost
  apply Eq.trans ?_ hs.symm
  apply Finset.sum_congr rfl
  intro l _
  simp only [geometryMainFirstCost,rows,mainLowSelectedNonzeroRows,Finset.mem_filter,
    Finset.mem_univ,true_and,vol,cost]

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_selected_complete_cost
