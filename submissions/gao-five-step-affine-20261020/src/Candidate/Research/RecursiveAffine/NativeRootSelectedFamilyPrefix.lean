/- Actual all-row prefix for the SAME canonical selected family. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalSelectedFamily
import Candidate.Research.RecursiveAffine.NativeActualRootRowPrefix

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentDivisorAllocation CenteredMomentSecondCanonical CenteredMomentFirstDiscardedEnergy
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle153RegionalLow Cycle153CanonicalLow
open Cycle153Reachable Cycle153HighProvider CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentOriginalCommonHarmonic CenteredMomentNaturalRowSource
variable {alpha beta Label : Type} [Fintype alpha] [DecidableEq alpha]
variable [Fintype beta] [DecidableEq beta] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}

/-- The source multiplier is the one produced by the native first/second
selected labels, on every row before any continuation test. Its genuine
prefix norm bound remains attached to the SAME canonical source family. -/
def CanonicalSelectedFamily.actualRootPrefix (C : SourceContext (α:=alpha) M H)
    (reflected second : Bool)(s : Input beta)
    (F0 : NaturalRow C.etaSeed 1)(R0 : Ideal O)(hparent : ParentPresentation s.η F0 R0)
    (Mrow amp xi reserve b firstHeight eps : ℝ)(budget : ℕ)
    (hMrow : Mrow≤2)(hamp : 0≤amp)(hloss : 0≤frequencyLoss C.globalBase 32 xi+reserve)
    (heps0 : 0≤eps)(heps : eps≤1)(hb : 0<b)
    (hsmall : Real.logb C.globalBase 4+2*(budget:ℝ)*Real.logb C.globalBase b+xi/2≤1)
    (hsource : sourceRadius s≤C.globalBase^(3:ℝ))
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (C.globalBase^Mrow) C.globalBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s 1 1 (C.globalBase^Mrow) C.globalBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val)
      1 s.ν s.W s.P≠0)
    (F : CanonicalSelectedFamily reflected second s 1 1 C.globalBase Mrow amp xi reserve b firstHeight budget
      C.globalBase_gt_one key hz1 hz2 firstIndex)
    (r : NativeLowRows reflected s 1 1 C.globalBase Mrow amp xi reserve b firstHeight budget
      C.globalBase_gt_one key hz1 hz2 firstIndex)(ray : RayFourExpansion.RayCharacter)
    (hP : (F.chain reflected second s 1 1 C.globalBase Mrow amp xi reserve b firstHeight budget
      C.globalBase_gt_one key hz1 hz2 firstIndex r).R₂*
      (F.chain reflected second s 1 1 C.globalBase Mrow amp xi reserve b firstHeight budget
        C.globalBase_gt_one key hz1 hz2 firstIndex r).E₂≠0)
    (hPN : (((F.chain reflected second s 1 1 C.globalBase Mrow amp xi reserve b firstHeight budget
      C.globalBase_gt_one key hz1 hz2 firstIndex r).R₂*
      (F.chain reflected second s 1 1 C.globalBase Mrow amp xi reserve b firstHeight budget
        C.globalBase_gt_one key hz1 hz2 firstIndex r).E₂).absNorm:ℝ)≤C.globalBase^(28:ℝ)) :=
  actualRootNativeRowPrefix C.etaSeed F0 R0 s hparent C.globalBase C.globalBase_gt_one C.Q
    reflected second Mrow amp xi reserve b firstHeight eps budget hMrow hamp hloss heps0 heps hb
    hsmall hsource key (firstIndex r.val.1) hz1 hz2 r.val.2
    (F.allocation r) (F.row r) (hf1 r.val.1) (F.frozen r) ray 28 hP hPN


end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.CanonicalSelectedFamily.actualRootPrefix
