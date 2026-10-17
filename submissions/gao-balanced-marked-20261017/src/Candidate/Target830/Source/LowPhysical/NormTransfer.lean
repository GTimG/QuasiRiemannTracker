import Candidate.Target830.Source.LowPhysical.BalancedTransfer

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.LowPhysical
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The same actual coefficient transport also applies before squared
Cauchy costs, for instance to the original zero or discarded-row terms. -/
theorem actual_balanced_scalar_norm_le (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    ‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j‖≤
      ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖ := by
  have h := actual_balanced_low_sum reflected s R seed K Z ξ M A hK hZ key weight
    {j} (fun _=>1) (by intros; norm_num)
  simp only [Finset.sum_singleton,mul_one] at h
  nlinarith [norm_nonneg (balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j),
    norm_nonneg (geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j)]

theorem actual_balanced_branch_norm_sum (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (J : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
    (cost : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)→ℝ)
    (hcost : ∀j∈J,0≤cost j) :
    (∑j∈J,‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j‖*cost j)≤
      ∑j∈J,‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖*cost j := by
  exact Finset.sum_le_sum (fun j hj=>mul_le_mul_of_nonneg_right
    (actual_balanced_scalar_norm_le reflected s R seed K Z ξ M A hK hZ key weight j) (hcost j hj))

end
end OAI.SevenEighths.Target830.Source.LowPhysical
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_balanced_scalar_norm_le
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_balanced_branch_norm_sum
