/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The active source radius contracts under the actual ordinary and marked
factor extraction when the original support/scales are at least one. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialPhysicalBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open QRH.Record1252270103Source.ForcedCost
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance initialPhysicalChildBoundsDecidable : DecidableEq ι:=Classical.decEq _

theorem sourceRadius_volume (s : Input ι) :
    sourceRadius s=(∏i,s.hi i)*s.b₁*s.b₂*volume s := by
  unfold sourceRadius volume
  ring

theorem child_source_radius_le (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hhi : ∀i,1≤s.hi i) (hP : ∀i,1≤s.P i) (hb₁ : 0≤s.b₁) (hb₂ : 0≤s.b₂) :
    sourceRadius (child s C R B τ t)≤sourceRadius s := by
  have hp : (∏i:liveIndices B.val,s.hi i.val)≤∏i,s.hi i := by
    rw [Finset.prod_coe_sort]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (hhi i)) (fun i _ _=>hhi i)
  have hv : volume (child s C R B τ t)≤volume s :=
    (child_volume_ordinary_bound s C R B τ t hP).trans
      (div_le_self (volume_pos s).le (ordinaryNorm_ge_one s C B))
  rw [sourceRadius_volume,sourceRadius_volume]
  change (∏i:liveIndices B.val,s.hi i.val)*s.b₁*s.b₂*volume (child s C R B τ t)≤_
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hb₁) hb₂) hv
    (volume_pos _).le
    (mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>zero_le_one.trans (hhi i))) hb₁) hb₂)

end
end QRH.Record1252270103Source.InitialPhysical
#print axioms QRH.Record1252270103Source.InitialPhysical.sourceRadius_volume
#print axioms QRH.Record1252270103Source.InitialPhysical.child_source_radius_le
