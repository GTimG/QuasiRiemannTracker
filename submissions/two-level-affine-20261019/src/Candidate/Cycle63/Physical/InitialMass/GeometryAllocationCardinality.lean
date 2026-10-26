/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAmplification

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O)
  (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
  (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
  (n N : ℕ) (hn : n≤N) (b : ℝ)
  (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
  (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))

include hn

/-- This changes only the outer allocation weight. The physical source and
its Fourier cutoff must retain their actual slot cardinality. -/
theorem geometry_allocation_weight_card_scale :
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B=
      (max 1 b)^(N-n)*geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight n b j B := by
  classical
  have hp : (max 1 b)^N=(max 1 b)^(N-n)*(max 1 b)^n := by
    rw [←pow_add,Nat.sub_add_cancel hn]
  unfold geometryAllocationWeight
  dsimp only
  split_ifs
  · rw [hp]
    ring
  · simp

theorem geometry_allocation_weight_card_mono :
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight n b j B≤
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B := by
  rw [geometry_allocation_weight_card_scale reflected s R seed K Z ξ M A hK key weight n N hn b j B]
  have hp : (1:ℝ)≤(max 1 b)^(N-n):=one_le_pow₀ (le_max_left 1 b)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
    (geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight n b j B)

end
end OAI.SevenEighths.Cycle63InitialMass
