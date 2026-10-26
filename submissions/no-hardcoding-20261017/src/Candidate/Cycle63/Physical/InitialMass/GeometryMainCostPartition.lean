/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCostReduction
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPartition

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentWholeDivisorShell
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

section Literal
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainCostPartitionSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
variable (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)


/-- The selected first cost is expanded without changing its original
nonzero filter. Complete second blocks remain inside each first index. -/
theorem actual_geometry_selected_cost_disintegration {Label : Type*} [Fintype Label]
    (first : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (mass : Label → ℝ) (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo : ℝ) (second : Bool) (t₀ u : ℝ) :
    (∑j,mass j*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u (first j))=
    ∑j,∑n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key (first j),
      if (⟨first j,n⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)∈
          geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
      then mass j/volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t (first j))*
        mainNormalizedBlockCost N slotlo plainlo second
          (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
            hz₁ hz₂ χ Q m ⟨first j,n⟩) t₀ u
      else 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [geometryMainFirstCost,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> ring

end Literal
section Rows
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- Literal normalized column cost, indexed by the actual physical row.
The reflected side changes both the ray character and the raw frequency. -/
def mainNormalizedPhysicalCost (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label → SecondInputDatum α) (coefficient : Label → ℝ) (t u : ℝ)
    (r : SecondRow (fun l=>(d l).block)) (D : Ideal O) : ℝ :=
  coefficient r.1*((d r.1).K/lowerFactor N a ap)*normalizer (d r.1).C (d r.1).D (d r.1).inactive*
    (if second then
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
        ((d r.1).input.t+2*Real.pi*(u-(-t))))
        (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2
    else
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
        ((d r.1).input.t+2*Real.pi*(u-t)))
        (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2)

/-- All rays and physical frequencies survive the block-to-row reindex. -/
theorem actual_main_block_cost_rows (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label → SecondInputDatum α) (coefficient : Label → ℝ) (t u : ℝ) :
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      ∑r∈secondLiveRows (fun l=>(d l).block),
        ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
          mainNormalizedPhysicalCost N a ap second d coefficient t u r D := by
  rw [actual_second_column_reindex]
  simp only [mainNormalizedBlockCost,mainNormalizedPhysicalCost,Finset.mul_sum,mul_assoc]

/-- The union of the complete family's second projectors is formed before
norm-shell grouping. The original membership test remains inside each shell. -/
theorem actual_main_block_cost_shared_shells (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label → SecondInputDatum α) (coefficient : Label → ℝ) (t u : ℝ) :
    let rows := secondLiveRows (fun l=>(d l).block)
    let Ds := fun r : rows=>secondResidualIdeals (fun l=>(d l).block) r.val
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      ∑n∈selectedShells (sharedProjectors Ds),∑r : rows,
        ∑D∈shell (sharedProjectors Ds) n,
          if D∈Ds r then mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D else 0 := by
  intro rows Ds
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort rows]
  apply shared_projector_shell_sum Ds
  intro r D hD
  exact (mem_second_residual_ideals (fun l=>(d l).block) r.val D).mp hD |>.2

end Rows

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_selected_cost_disintegration
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_block_cost_rows
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_block_cost_shared_shells
