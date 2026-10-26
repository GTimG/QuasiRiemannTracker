import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowPhysicalPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondFullNormalizedContraction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondLiveBlock CenteredMomentSourceRow
open LocalMoment CenteredMomentSecondInputCapacitySource CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondEnergySplit ConcretePrimeRowBridge

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- Lift the per-source selector to the physical family before dividing it
into low and high rows. The signed row and its original block are unchanged. -/
def mainPhysicalFamilySelector (second : Bool) (d : Label→SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    secondLiveRows (fun l=>(d l).block)→BufferIndex e :=
  fun r=>select r.val.1 r.val.2.1 r.val.2.2.1
    ⟨mainLowSignedRow second r.val.2.2.2.val,by
      apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
      refine ⟨r.val.2.2.2,?_,rfl,True.intro⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩⟩

variable [Cycle63.AffineLedger] in
theorem main_low_physical_predicate_iff (second : Bool) (d : Label→SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (r : secondLiveRows (fun l=>(d l).block)) :
    mainLowPhysicalSourcePredicate (mainLowSourceRows second (d r.val.1) (fun _=>True))
      (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val) ↔
    bufferValue e (mainPhysicalFamilySelector second d select r)<((1+Cycle63.AffineLedger.q)/2) := by
  have hz : mainLowSignedRow second r.val.2.2.2.val∈
      mainLowSourceRows second (d r.val.1) (fun _=>True) := by
    apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
    exact ⟨r.val.2.2.2,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩,rfl,True.intro⟩
  simp only [mainLowPhysicalSourcePredicate,dite_eq_left hz,mainPhysicalFamilySelector]

variable [Cycle63.AffineLedger] in
/-- Exact complementary physical costs on one selector. Both ray sums,
both signed Mellin heights, the lower factor, and all residual divisors remain
literal. No arithmetic-label or allocation count is introduced. -/
theorem actual_main_complete_low_high_partition
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      mainLowPhysicalCompleteCost N a ap second d coefficient t u select+
      ∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(d l).block)=>
        ((1+Cycle63.AffineLedger.q)/2)≤bufferValue e (mainPhysicalFamilySelector second d select r)),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort]
  rw [actual_main_low_physical_ordinary_row_cost]
  unfold mainLowPhysicalOrdinaryRows
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
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
  have hp:=main_low_physical_predicate_iff second d select r
  by_cases hl : bufferValue e (mainPhysicalFamilySelector second d select r)<((1+Cycle63.AffineLedger.q)/2)
  · simp only [hp,hl,ite_true,not_le.mpr hl,ite_false,add_zero]
  · simp only [hp,hl,ite_false,le_of_not_gt hl,ite_true,zero_add]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
