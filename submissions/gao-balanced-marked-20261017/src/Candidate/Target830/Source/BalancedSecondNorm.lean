import Candidate.Target830.Source.BalancedSecondWeight

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The complete actual second block is controlled by its original
balanced first-allocation weight, in either physical orientation. -/
theorem balanced_main_block_weight_norm
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    ‖balancedMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j‖≤
      balancedLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1 := by
  rw [balancedMainSecondWeight_eq]
  rw [balancedLowFirstWeight_eq reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (zero_lt_one.trans hZ) key weight b t j.1]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)]
  exact mul_le_mul_of_nonneg_right
    (actual_geometry_main_block_weight_norm reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      Mprice Aprice weight j) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

end
end OAI.SevenEighths.Target830.Source
#print axioms OAI.SevenEighths.Target830.Source.balanced_main_block_weight_norm
