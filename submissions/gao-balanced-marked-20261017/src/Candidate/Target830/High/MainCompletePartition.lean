import Candidate.Target830.Parameters
import Candidate.Target830.Source.LowPhysical.MainLowPhysicalCost
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPhysicalPayment
import Candidate.Cycle63.Physical.InitialMass.SecondFullNormalizedContraction

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.TargetHigh830
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondLiveBlock CenteredMomentSourceRow
open LocalMoment CenteredMomentSecondInputCapacitySource CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondEnergySplit ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem main_low_physical_predicate_iff (plane : SourcePlane) (second : Bool) (d : Label→SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (r : secondLiveRows (fun l=>(d l).block)) :
    Target830.Source.LowPhysical.mainLowPhysicalSourcePredicate (P:=plane) (mainLowSourceRows second (d r.val.1) (fun _=>True))
      (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val) ↔
    bufferValue e (mainPhysicalFamilySelector second d select r)<(1+plane.q)/2 := by
  have hz : mainLowSignedRow second r.val.2.2.2.val∈
      mainLowSourceRows second (d r.val.1) (fun _=>True) := by
    apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
    exact ⟨r.val.2.2.2,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩,rfl,True.intro⟩
  simp only [Target830.Source.LowPhysical.mainLowPhysicalSourcePredicate,dite_eq_left hz,mainPhysicalFamilySelector]

/-- Exact complementary physical costs on one selector. Both ray sums,
both signed Mellin heights, the lower factor, and all residual divisors remain
literal. No arithmetic-label or allocation count is introduced. -/
theorem actual_main_complete_low_high_partition (plane : SourcePlane)
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      Target830.Source.LowPhysical.mainLowPhysicalCompleteCost (P:=plane) N a ap second d coefficient t u select+
      ∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(d l).block)=>
        (1+plane.q)/2≤bufferValue e (mainPhysicalFamilySelector second d select r)),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort]
  rw [Target830.Source.LowPhysical.actual_main_low_physical_ordinary_row_cost]
  unfold Target830.Source.LowPhysical.mainLowPhysicalOrdinaryRows
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hcost : (∑D∈secondResidualIdeals (fun l=>(d l).block) r.val,
      mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D)=
      (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
        normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
      highNormalizedRowCost second d r
        ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
        ((d r.val.1).block.divisors.filter Squarefree) := by
    rw [actual_second_residual_ideals_label]
    cases second <;> simp [mainNormalizedPhysicalCost,highNormalizedRowCost,Finset.mul_sum]
  rw [hcost]
  have hp:=main_low_physical_predicate_iff plane second d select r
  by_cases hl : bufferValue e (mainPhysicalFamilySelector second d select r)<(1+plane.q)/2
  · simp only [hp,hl,ite_true,not_le.mpr hl,ite_false,add_zero]
  · simp only [hp,hl,ite_false,le_of_not_gt hl,ite_true,zero_add]


end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_main_complete_low_high_partition
