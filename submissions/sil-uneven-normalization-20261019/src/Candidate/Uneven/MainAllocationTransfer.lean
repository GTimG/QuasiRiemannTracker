/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.SecondWeight
import Candidate.Cycle63.Physical.InitialMass.GeometryAmplification

set_option autoImplicit false
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open scoped Classical BigOperators
open Target830.Source.Uneven HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentOriginalCommonHarmonic Cycle63InitialMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unequal normalization decreases every nonnegative allocation cost. -/
theorem actual_uneven_allocation_weight_le (reflected : Bool) (s : Input ι)
    (R seed : Ideal O) (K Z ξ M A : ℝ) (hK : 0<K) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) :
    unevenAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B ≤
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B := by
  rw [unevenAllocationWeight_eq reflected s R seed K Z ξ M A hK
    (zero_lt_one.trans hZ) key weight N b j B]
  have ha := actual_allocation_nonneg reflected s R seed K Z ξ hZ j.1.val
  have hp : Z^(-allocation reflected (geometryExponents s R seed K Z ξ j.1.val)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  exact (mul_le_mul_of_nonneg_left hp
    (geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j B)).trans_eq
    (mul_one _)

end
end OAI.SevenEighths.MainAssembly
