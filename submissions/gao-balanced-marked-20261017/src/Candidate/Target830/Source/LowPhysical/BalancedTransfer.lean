import Candidate.Target830.Source.BalancedColumns
import Candidate.Cycle63.Physical.InitialMass.GeometryLowSidePayment

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.LowPhysical
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentOriginalCommonHarmonic
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonnegative LOW branch cost retains its actual column, profile,
allocation and row tests while the new balanced scalar is inserted. -/
theorem actual_balanced_low_sum (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (J : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
    (cost : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)→ℝ)
    (hcost : ∀j∈J,0≤cost j) :
    (∑j∈J,‖balancedColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*cost j) ≤
      ∑j∈J,‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*cost j := by
  apply Finset.sum_le_sum
  intro j hj
  rw [balancedColumnScalar_norm_sq reflected s R seed K Z ξ M A hK key weight j
    (zero_lt_one.trans hZ)]
  have hSigma := actual_surplus_nonneg s R seed K Z ξ hZ j.1.val
  have hp : Z^(-surplus (geometryExponents s R seed K Z ξ j.1.val))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  have hn := mul_le_mul_of_nonneg_left hp (sq_nonneg
    ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖)
  simpa only [mul_one] using mul_le_mul_of_nonneg_right hn (hcost j hj)

/-- The actual LOW scalar uses the balanced side and keeps the full
negative common surplus, rather than replacing it by an independent box. -/
theorem actual_balanced_low_exponent (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    let v := geometryExponents s R seed K Z ξ j.1.val
    v 2+lowGeometryExponent reflected Z A (geometryFirstLabel s R seed K Z ξ hK key j)-
      (if reflected then balancedRight A v else balancedLeft A v)=
      -(max (3*v (if reflected then 1 else 0)-5*v (if reflected then 0 else 1)-v 3) 0/6)-
        surplus v := by
  intro v
  rw [actual_low_geometry_exponent_coordinates]
  cases reflected <;>
    simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [left_eq_old]
    dsimp only [Cycle63InitialMass.leftExponent]
    ring
  · rw [right_eq_old]
    dsimp only [Cycle63InitialMass.rightExponent]
    ring

end
end OAI.SevenEighths.Target830.Source.LowPhysical
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_balanced_low_sum
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_balanced_low_exponent
