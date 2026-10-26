/- SAME actual root selected prefix, chosen once before continuation. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootPrefix

set_option autoImplicit false
set_option maxHeartbeats 1000000
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
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentSourceLiveColumn Cycle153HighProvider Cycle153JointCount

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The literal root counterpart of actualNativeRowPrefix; the same value is
reused by Columns and all later continuations. No child output is assumed. -/
def actualRootNativeRowPrefix
    (etaSeed : Character) (F0 : NaturalRow etaSeed 1) (R0 : Ideal O)
    (s : Input α) (hparent : ParentPresentation s.η F0 R0)
    (Z : ℝ) (hZ : 1<Z) (Q : Ideal O)
    (reflected second : Bool) (Mrow amp xi reserve b t eps : ℝ) (budget : ℕ)
    (hMrow : Mrow ≤ 2) (hamp : 0 ≤ amp) (hloss : 0 ≤ frequencyLoss Z 32 xi+reserve)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1) (hb : 0<b)
    (hsmall : Real.logb Z 4+2*(budget:ℝ)*Real.logb Z b+xi/2 ≤ 1)
    (hsource : sourceRadius s ≤ Z^(3:ℝ))
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s 1 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s 1 1 Z Mrow amp xi reserve b t budget hZ bin q) :
    let datum:=geometryLowSecondDatum reflected s 1 1 Z Mrow amp xi reserve b t budget hZ bin q hz1 hz2 n
    let src:=geometryLowFirstChild reflected s 1 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
    ∀(allocation : actualAllocations src.pools (if second then datum.D else datum.C))
      (r : secondLiveRows (fun _:Unit=>datum.block))
      (hf1 : frozenCoefficient q.2.val (geometryColumnIdeal reflected s 1 1 (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) 1 s.ν s.W s.P≠0)
      (hf2 : frozenCoefficient allocation.val (if second then datum.D else datum.C)
        datum.R src.ν src.W src.P≠0) (chi : RayCharacter) (Bmask : ℝ),
    let chain:=geometryLowActualChain reflected s 1 1 Z Mrow amp xi reserve b t budget hZ bin q hz1 hz2 n second allocation
    let g:=geometryLowActualGeometry reflected s 1 1 Z Mrow amp xi reserve b t budget hZ bin q hz1 hz2 n second allocation r hf1 hf2
    ∀(hP : chain.R₂*chain.E₂≠0) (hPN : ((chain.R₂*chain.E₂).absNorm:ℝ) ≤ Z^Bmask),
    let st:=retainedState Z Bmask hZ (g.datum.τ chi) (internalQ Q etaSeed)
      (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let first:=geometryFirstLabel s 1 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
    let label:=actualSecondArithmeticLabel _ _ _ _ _ _ _ n
    let units:=fun l=>(firstDictionaryUnit (!reflected) etaSeed 1 F0 R0 l:O)
    {Next : PrefixHighPresentation (secondFixedDictionary etaSeed) st.character st.puncture //
      Next.mult=Cycle63Moment.childMultiplier (!reflected) 1 units ⟨first,label⟩ ∧
      ((Ideal.span {Next.mult}).absNorm:ℝ) ≤ Z^prefixCap 0 ∧
      st.rowWidth+Real.logb Z ((Ideal.span {Next.mult}).absNorm:ℝ) ≤
        actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
          Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 2+
        (Real.logb Z 4+2*(budget:ℝ)*Real.logb Z b+xi/2) } := by
  intro datum src allocation r hf1 hf2 chi Bmask chain g hP hPN st first label units
  let proof := actual_root_native_prefix etaSeed F0 R0 s hparent Z hZ Q reflected second
    Mrow amp xi reserve b t eps budget hMrow hamp hloss heps0 heps hb hsmall hsource
    bin q hz1 hz2 n allocation r hf1 hf2 chi Bmask hP hPN
  exact ⟨Classical.choose proof, Classical.choose_spec proof⟩

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actualRootNativeRowPrefix
