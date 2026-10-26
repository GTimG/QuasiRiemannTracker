import Candidate.Target830.Source.BalancedAllocationTransfer
import Candidate.Cycle63.Physical.InitialMass.GeometryCostSelection
set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63InitialMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentLogDyadic
open CenteredMomentFirstAmplificationChoice CenteredMomentPrimeElements RayFourExpansion
local notation "O" => HeckeFamily.O

/-- ERROR costs are positive, so the balanced allocation comparison can be
performed before their complete prime/ray/branch sums are estimated. -/
theorem balanced_error_cost_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A sigma reserve b t : ℝ) (hK : 0<K) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ)
    (P : Finset (Ideal O))
    (τ : (j : ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus)))→
      actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val)→
      elementPool P→Fin 3→RayCharacter→Character) :
    (∑j : ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus)),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val),
      balancedAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val B*
        actualErrorSources
          (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val) R B
            (geometryColumnCharacter reflected s R seed K Z ξ hK key j.val) t)
          (geometryBranch reflected s R seed K Z ξ hK key j.val) Z sigma 1 ξ reserve P (τ j B))≤
    ∑j : ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus)),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val),
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val B*
        actualErrorSources
          (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val) R B
            (geometryColumnCharacter reflected s R seed K Z ξ hK key j.val) t)
          (geometryBranch reflected s R seed K Z ξ hK key j.val) Z sigma 1 ξ reserve P (τ j B) := by
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro B _
  exact mul_le_mul_of_nonneg_right
    (actual_balanced_allocation_weight_le reflected s R seed K Z ξ M A hK hZ key weight N b j.val B)
    (actual_error_sources_nonneg _ _ _ _ _ _ _ (zero_lt_one.trans hZ) _ _)
end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.balanced_error_cost_le
