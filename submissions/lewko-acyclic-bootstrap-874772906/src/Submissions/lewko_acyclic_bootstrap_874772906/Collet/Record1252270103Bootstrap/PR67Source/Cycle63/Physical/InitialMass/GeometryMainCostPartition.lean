import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainCostReduction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondProjectorShell
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryZeroPartition
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
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

section Literal
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainCostPartitionSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
variable (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)

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

end Rows

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
