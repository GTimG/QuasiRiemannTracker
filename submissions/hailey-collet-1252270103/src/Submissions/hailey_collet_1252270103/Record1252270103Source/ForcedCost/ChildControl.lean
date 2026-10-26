/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonExceptionalCost
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ForcedCost
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedDetectorAmplitude
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq ι := Classical.decEq _

theorem child_slotControl (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    slotControl (child s C R B τ t).toData≤slotControl s.toData := by
  change slotControl (commonData s C R B)≤slotControl s.toData
  exact CenteredMomentCommonExceptionalCost.common_slotControl s C R B

theorem child_scales_ge_one (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hP : ∀i,1≤s.P i) : ∀i,1≤(child s C R B τ t).P i :=
  fun i=>hP i.val
end
end QRH.Record1252270103Source.ForcedCost
#print axioms QRH.Record1252270103Source.ForcedCost.child_slotControl
#print axioms QRH.Record1252270103Source.ForcedCost.child_scales_ge_one
