import Candidate.Target830.Source.BalancedAmplification
import Candidate.Target830.Source.LowPhysical.NormTransfer
import Candidate.Cycle63.Physical.InitialMass.GeometryAmplification

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonAllocationSum
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On an actual allocation, the balanced weight decreases every
nonnegative cost. This comparison is used only outside the HIGH saving. -/
theorem actual_balanced_allocation_weight_le (reflected : Bool) (s : Input ι)
    (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) :
    balancedAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B≤
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B := by
  have hn := LowPhysical.actual_balanced_scalar_norm_le reflected s R seed K Z ξ M A hK hZ key weight j
  have hn₂ : ‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2≤
      ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2 := by
    nlinarith [norm_nonneg (balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j),
      norm_nonneg (geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j)]
  unfold balancedAllocationWeight geometryAllocationWeight
  dsimp only
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn₂ (by positivity)) (sq_nonneg _)
  · exact le_rfl

theorem actual_balanced_allocation_cost_sum_le (reflected : Bool) (s : Input ι)
    (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (b : ℝ)
    (J : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
    (cost : (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))→
      actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)→ℝ)
    (hcost : ∀j∈J,∀B,0≤cost j B) :
    (∑j∈J,∑B,balancedAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B*cost j B)≤
      ∑j∈J,∑B,geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B*cost j B := by
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro B _
  exact mul_le_mul_of_nonneg_right
    (actual_balanced_allocation_weight_le reflected s R seed K Z ξ M A hK hZ key weight N b j B)
    (hcost j hj B)

end
end OAI.SevenEighths.Target830.Source
#print axioms OAI.SevenEighths.Target830.Source.actual_balanced_allocation_weight_le
#print axioms OAI.SevenEighths.Target830.Source.actual_balanced_allocation_cost_sum_le
