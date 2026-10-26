import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighResidualAllocation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.HighSourceEnergy
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

lemma diagonal_retained_cost_le_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Data ι) (L : Ideal O) (z : O) :
    (∑ alloc ∈ s.toSource.active L, retainedAllocationCost s L alloc z) ≤
      ∑ a ∈ s.toSource.active L, ∑ b ∈ s.toSource.active L,
        Real.sqrt (retainedAllocationCost s L a z) *
          Real.sqrt (retainedAllocationCost s L b z) := by
  refine Finset.sum_le_sum fun a ha => ?_
  calc
    _ = Real.sqrt (retainedAllocationCost s L a z) *
        Real.sqrt (retainedAllocationCost s L a z) :=
      (Real.mul_self_sqrt (retained_allocation_cost_nonneg s L a z)).symm
    _ ≤ _ := Finset.single_le_sum (s := s.toSource.active L)
      (f := fun b => Real.sqrt (retainedAllocationCost s L a z)*
        Real.sqrt (retainedAllocationCost s L b z))
      (fun b _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ha

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
