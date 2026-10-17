import Candidate.Target830.Parameters
import Candidate.Target830.Source.LowPhysical.MainLowPhysicalCost
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainSelectedCompleteCost
import Candidate.Target830.High.MainCompletePartition

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource LocalMoment
open CenteredMomentSecondCanonicalScalar
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance selectedPartitionSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- Partition the exact supported first-selection cost on its complete
second family. The low and high bounds share one selector and preserve the
original full-zero filter. No selected-label count is introduced. -/
theorem actual_main_selected_low_high_cost (plane : SourcePlane)
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (mass : Label→ℝ) (χ : RayCharacter) (Q : Ideal O) (m : O)
    (a ap : ℝ) (second : Bool) (t₀ u : ℝ) :
    let rows := mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ firstIndex
    let datum := fun r : rows=>geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m ⟨firstIndex r.val.1,r.val.2⟩
    let coefficient := fun r : rows=>mass r.val.1/volume
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t (firstIndex r.val.1))
    ∀(e : ℝ)(select : (r : rows)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (datum r) (fun _=>True)→BufferIndex e)(CL CH : ℝ),
    Target830.Source.LowPhysical.mainLowPhysicalCompleteCost (P:=plane) N a ap second datum coefficient t₀ u select≤CL →
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(datum l).block)=>
      (1+plane.q)/2≤bufferValue e (mainPhysicalFamilySelector second datum select r)),
      (coefficient r.val.1*((datum r.val.1).K/lowerFactor N a ap)*
        normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)*
      highNormalizedRowCost second datum r
        ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.1).block.divisors.filter Squarefree))≤CH →
    (∑l,mass l*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m a ap second t₀ u (firstIndex l))≤CL+CH := by
  intro rows datum coefficient e select CL CH hlow hhigh
  have he := actual_main_selected_complete_cost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ firstIndex mass χ Q m a ap second t₀ u
  change _=(∑r : rows,coefficient r*mainNormalizedBlockCost N a ap second (datum r) t₀ u) at he
  rw [he,actual_main_complete_low_high_partition plane N a ap second datum coefficient t₀ u select]
  exact add_le_add hlow hhigh

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_main_selected_low_high_cost
