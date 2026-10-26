/- Adapted from PR63 by Sil, with OpenAI Codex assistance.
   Original attribution and Apache-2.0 license are retained. -/
import Candidate.Uneven.SecondWeight

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Uneven
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The complete actual second block is controlled by its original
uneven first-allocation weight, in either physical orientation. -/
theorem uneven_main_block_weight_norm
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key) :
    ‖unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j‖≤
      unevenLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.1 := by
  rw [unevenMainSecondWeight_eq]
  rw [unevenLowFirstWeight_eq reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (zero_lt_one.trans hZ) key weight b t j.1]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)]
  exact mul_le_mul_of_nonneg_right
    (actual_geometry_main_block_weight_norm reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      Mprice Aprice weight j) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

end
end OAI.SevenEighths.Target830.Source.Uneven
