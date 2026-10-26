/- Named actual all-row prefix, selected once before continuation and reused by Columns.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualNativePrefix

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondInputCapacitySource Cycle63FinalNatural Cycle63FinalLow
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredMomentNaturalFixedRaySource CenteredMomentSourceLiveColumn Cycle153HighProvider Cycle153JointCount

variable {α : Type} [Fintype α] [DecidableEq α]
variable {β : Type} [Fintype β] [DecidableEq β]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

def actualNativeRowPrefix (N : ReachableNode C j)
    (s : Input β) (R : Ideal O)
    (P0 : PrefixHighPresentation (prefixDictionary j.val C.etaSeed) s.η R)
    (hP0mult : P0.mult=N.presentation.mult)
    (reflected second : Bool) (Mrow amp xi reserve b t eps : ℝ) (budget : ℕ)
    (hMrow : Mrow≤2) (hamp : 0≤amp) (hloss : 0≤frequencyLoss N.localBase 32 xi+reserve)
    (heps0 : 0≤eps) (heps : eps≤1) (hb : 0<b)
    (hsmall : Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2≤1)
    (hsource : sourceRadius s≤N.localBase^(3:ℝ))
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R 1
      (N.localBase^Mrow) N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin)
    (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R 1 N.localBase Mrow amp xi reserve
      b t budget N.localBase_gt_one bin q) :
    let datum:=geometryLowSecondDatum reflected s R 1 N.localBase Mrow amp xi reserve b t
      budget N.localBase_gt_one bin q hz1 hz2 n
    let src:=geometryLowFirstChild reflected s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin t q
    ∀(allocation : actualAllocations src.pools (if second then datum.D else datum.C))
      (r : secondLiveRows (fun _:Unit=>datum.block))
      (hf1 : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R 1
        (N.localBase^Mrow) N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _)
        bin q.1.val) R s.ν s.W s.P≠0)
      (hf2 : frozenCoefficient allocation.val (if second then datum.D else datum.C)
        datum.R src.ν src.W src.P≠0) (chi : RayCharacter) (Bmask : ℝ),
    let chain:=geometryLowActualChain reflected s R 1 N.localBase Mrow amp xi reserve b t
      budget N.localBase_gt_one bin q hz1 hz2 n second allocation
    let g:=geometryLowActualGeometry reflected s R 1 N.localBase Mrow amp xi reserve b t
      budget N.localBase_gt_one bin q hz1 hz2 n second allocation r hf1 hf2
    ∀(hP : chain.R₂*chain.E₂≠0) (hPN : ((chain.R₂*chain.E₂).absNorm:ℝ)≤N.localBase^Bmask),
    let st:=retainedState N.localBase Bmask N.localBase_gt_one (g.datum.τ chi) (internalQ C.Q C.etaSeed)
      (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let first:=geometryFirstLabel s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin q.1.val
    let label:=actualSecondArithmeticLabel _ _ _ _ _ _ _ n
    {Next : PrefixHighPresentation (prefixDictionary (j.val+1) C.etaSeed) st.character st.puncture //
      Next.mult=Cycle63Moment.childMultiplier (!reflected) P0.mult (P0.unit (!reflected)) ⟨first,label⟩ ∧
      ((Ideal.span {Next.mult}).absNorm:ℝ)≤C.globalBase^prefixCap (j.val+1) ∧
      N.unit*st.rowWidth+Real.logb C.globalBase ((Ideal.span {Next.mult}).absNorm:ℝ)-
        Real.logb C.globalBase ((Ideal.span {P0.mult}).absNorm:ℝ) ≤
        N.unit*actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
          N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve eps 2+
        N.unit*(Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2) } := by
  intro datum src allocation r hf1 hf2 chi Bmask chain g hP hPN st first label
  let proof:=actual_native_continuation_prefix N s R P0 hP0mult reflected second
    Mrow amp xi reserve b t eps budget hMrow hamp hloss heps0 heps hb hsmall hsource bin q hz1 hz2 n
    allocation r hf1 hf2 chi Bmask hP hPN
  exact ⟨Classical.choose proof,Classical.choose_spec proof⟩

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actualNativeRowPrefix
