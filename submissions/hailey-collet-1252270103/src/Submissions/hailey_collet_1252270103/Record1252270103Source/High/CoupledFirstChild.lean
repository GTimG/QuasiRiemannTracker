/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The allocated modified coefficient is the literal child Input coefficient.
The common divisor pulls back the tuple modifier without weakening its mask. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstAllocation
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput Record1252270103Source
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance coupledFirstChildDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma modifiedBeta_original (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O) :
    modifiedBeta (original s R seed) modifier=coefficient s modifier R seed := rfl

/-- Exact first-to-second child inlet. No ordinary-column nonzero premise. -/
theorem allocated_modifiedBeta_child (s:Input ι)(modifier:Tuple ι→ℂ)(C R seed L:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ) :
    modifiedBeta (allocatedData (original s R seed) C L B) (pulledModifier B.val modifier)=
      coefficient (child s C R B τ t) (pulledModifier B.val modifier) (R*C) L := by
  change finiteColumnCoefficient (CenteredMomentSourceLiveColumn.liveBox s.pools B.val _)
    (fun v=>pulledModifier B.val modifier v*
      CenteredMomentAmplificationLiveMask.maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂
        s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 v)=_
  rw [child_tuplePool s C R B τ t,child_profile s C R L B τ t]
  unfold coefficient tupleCoefficient
  apply congrArg (fun S=>finiteColumnCoefficient S _)
  ext v
  simp only [Fintype.mem_piFinset]

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.modifiedBeta_original
#print axioms QRH.Record1252270103Source.High.CoupledFirst.allocated_modifiedBeta_child
