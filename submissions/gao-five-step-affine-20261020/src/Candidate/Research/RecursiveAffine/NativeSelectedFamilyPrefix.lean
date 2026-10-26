/- Actual all-row prefix for the SAME canonical selected family. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalSelectedFamily
import Candidate.Research.RecursiveAffine.NativeActualRowPrefix

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
open CenteredMomentOriginalCommonHarmonic
variable {alpha beta Label : Type} [Fintype alpha] [DecidableEq alpha]
variable [Fintype beta] [DecidableEq beta] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- The source multiplier is the one produced by the native first/second
selected labels, on every row before any continuation test. Its genuine
prefix norm bound remains attached to the SAME canonical source family. -/
def CanonicalSelectedFamily.actualPrefix (N : ReachableNode C j)
    (reflected second : Bool)(s : Input beta)(R : Ideal O)
    (P0 : PrefixHighPresentation (prefixDictionary j.val C.etaSeed) s.η R)
    (hP0mult : P0.mult=N.presentation.mult)
    (Mrow amp xi reserve b firstHeight eps : ℝ)(budget : ℕ)
    (hMrow : Mrow≤2)(hamp : 0≤amp)(hloss : 0≤frequencyLoss N.localBase 32 xi+reserve)
    (heps0 : 0≤eps)(heps : eps≤1)(hb : 0<b)
    (hsmall : Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2≤1)
    (hsource : sourceRadius s≤N.localBase^(3:ℝ))
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R 1 (N.localBase^Mrow) N.localBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val)
      R s.ν s.W s.P≠0)
    (F : CanonicalSelectedFamily reflected second s R 1 N.localBase Mrow amp xi reserve b firstHeight budget
      N.localBase_gt_one key hz1 hz2 firstIndex)
    (r : NativeLowRows reflected s R 1 N.localBase Mrow amp xi reserve b firstHeight budget
      N.localBase_gt_one key hz1 hz2 firstIndex)(ray : RayFourExpansion.RayCharacter)
    (hP : (F.chain reflected second s R 1 N.localBase Mrow amp xi reserve b firstHeight budget
      N.localBase_gt_one key hz1 hz2 firstIndex r).R₂*
      (F.chain reflected second s R 1 N.localBase Mrow amp xi reserve b firstHeight budget
        N.localBase_gt_one key hz1 hz2 firstIndex r).E₂≠0)
    (hPN : (((F.chain reflected second s R 1 N.localBase Mrow amp xi reserve b firstHeight budget
      N.localBase_gt_one key hz1 hz2 firstIndex r).R₂*
      (F.chain reflected second s R 1 N.localBase Mrow amp xi reserve b firstHeight budget
        N.localBase_gt_one key hz1 hz2 firstIndex r).E₂).absNorm:ℝ)≤N.localBase^(28:ℝ)) :=
  actualNativeRowPrefix N s R P0 hP0mult reflected second Mrow amp xi reserve b firstHeight eps budget
    hMrow hamp hloss heps0 heps hb hsmall hsource key (firstIndex r.val.1) hz1 hz2 r.val.2
    (F.allocation r) (F.row r) (hf1 r.val.1) (F.frozen r) ray 28 hP hPN

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.CanonicalSelectedFamily.actualPrefix
