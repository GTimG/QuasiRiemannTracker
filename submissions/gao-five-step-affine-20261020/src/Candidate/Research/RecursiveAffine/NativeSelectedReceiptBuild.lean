/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedReceipt
import Candidate.Research.RecursiveAffine.NativeSelectedChronology
import Candidate.Research.RecursiveAffine.NativeWholeNodeForest
import Candidate.Research.RecursiveAffine.ActualTraceTransport
import Candidate.Research.RecursiveAffine.PhysicalStepCoordinates

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
set_option maxRecDepth 4000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization Cycle153SourceReturn Cycle153Reachable Cycle153JointCount

variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H} {j : Fin 4}
variable (parent : ReachableNode C j) (hj : j.val < 3)
variable (reflected second : Bool) (s : Input parent.slots) (R seed : Ideal O)
variable (Mrow amp xi reserve eps b firstHeight : ℝ) (budget : ℕ)
variable (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
variable (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (parent.localBase^Mrow)
  parent.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans parent.localBase_gt_one) _) key)

local notation "Rows" => NativeLowRows reflected s R seed parent.localBase Mrow amp xi reserve b
  firstHeight budget parent.localBase_gt_one key hz1 hz2 firstIndex
local notation "first" => fun l=>geometryFirstLabel s R seed (parent.localBase^Mrow) parent.localBase xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans parent.localBase_gt_one) _) key (firstIndex l).1.val
local notation "rowKey" => nativeLowHistoryCode reflected s R seed parent.localBase Mrow amp xi reserve b
  firstHeight budget parent.localBase_gt_one key hz1 hz2 firstIndex
local notation "childRoot" => fun r : Rows=>Cycle63Moment.childMultiplier (!reflected)
  parent.presentation.mult units (rowKey r).1

private theorem selected_part_fields
    {BType : Type} {q Z Bnorm T : ℝ} {dict : Character→BType→Character}
    {eta : Character} {v v' : O}
    (a : ReturnedPartAt M H hH q dict eta Z Bnorm T v)
    (a' : ReturnedPartAt M H hH q dict eta Z Bnorm T v')
    (hv : v=v') (he : HEq a a') :
    a.scale=a'.scale ∧ a.length=a'.length ∧ a.amp=a'.amp := by
  cases hv
  have h:=eq_of_heq he
  cases h
  exact ⟨rfl,rfl,rfl⟩

attribute [local irreducible] geometryFirstLabel actualHighCoordinates

/-- Construct the entire arithmetic receipt on the literal selected LOW
forest. Every continuing terminal is grafted from its actual child trace
and native source edge; all zero branches have empty carriers. Varying
reflection words are glued by the actual full source-key injection. -/
def actual_native_selected_receipt
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH (innerStage j.val).q (prefixDictionary (j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz parent.presentation.mult)
    (w : parent.slots→ℝ) (deleted : Rows→Finset parent.slots) (q : ℝ) (fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1)) C.etaSeed
      parent.localBase C.Bnorm C.Tz (Cycle63Moment.childMultiplier (!reflected)
        parent.presentation.mult units (rowKey r).1))
    (Bsrc : ℝ) (boxes : ℕ→Finset (Fin 4→ℤ))
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
    (sourceFacts : ∀r : Rows,DecoratedFacts (fun _ : Unit=>parent.presentation.mult) (!reflected)
      (fun _=>units) parent.localBase Bsrc (boxes 0) ((),rowKey r))
    (histories : ∀r,OrientedFamilyHistory (children r) (suffixOffset (4-(j.val+1)))
      Bsrc (fun k=>boxes (k+1)))
    (hm : own.scale=parent.state.rowWidth)
    (hA : own.length=Real.logb parent.localBase (volume (parent.input hH)))
    (ampError : ℝ) (hAmp0 : 0 ≤ ampError) (hAmpFine : ampError ≤ 1/1000000000000)
    (hAmp : parent.unit*own.amp ≤
      ![Cycle153Geometry.Coordinates.a1 parent.coordinates,Cycle153Geometry.Coordinates.a2 parent.coordinates,
        Cycle153Geometry.Coordinates.a3 parent.coordinates,Cycle153Geometry.Coordinates.a4 parent.coordinates] j+ampError)
    (ownLoss : own.loss ≤ terminalLossCap j)
    (ownSource : TerminalSourceCaps own.scale own.length own.amp
      (Real.logb parent.localBase ((Ideal.span {parent.presentation.mult}).absNorm:ℝ)))
    (ownClass : ∀b,(Fintype.card (own.record b).Class:ℝ) ≤ C.highClassCap)
    (childrenLoss : ∀r d p,((children r).part d p).loss ≤ terminalLossCap j)
    (childrenSource : ∀r d p,TerminalSourceCaps ((children r).part d p).scale
      ((children r).part d p).length ((children r).part d p).amp
      (Real.logb parent.localBase ((Ideal.span {(children r).multiplier d p}).absNorm:ℝ)))
    (childrenClass : ∀r d p b,(Fintype.card (((children r).part d p).record b).Class:ℝ) ≤ C.highClassCap)
    (paths : ∀r d p,NativeSelectedChildPath parent hj reflected s R seed Mrow amp xi reserve b
      firstHeight budget key hz1 hz2 firstIndex units children
      (fun r=>parent.localBase^(Mrow+
        actualHighCoordinates reflected (!reflected) second (first r.val.1)
          (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2
          parent.localBase Mrow (Real.logb parent.localBase (volume s)) amp xi reserve eps 0+
          q*(∑i∈deleted r,w i)+fees r))
      (fun r=>Real.logb parent.localBase ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ)) r d p) :
    NativeNodeForestReceipt hH parent Bsrc boxes := by
  let F:=actualNativeSuffixRows parent hj reflected second s R seed Mrow amp xi reserve eps b firstHeight
    budget key hz1 hz2 firstIndex units own w deleted q fees children
  refine { family:=F,chronology:=?_,path:=?_,terminalLoss:=?_,terminalSource:=?_,classCap:=?_ }
  · apply Classical.choice
    change Nonempty (ForestChronology hH parent F Bsrc boxes)
    have hn : ∀d : SuffixDepth (4-(j.val+1)),suffixOffset (4-(j.val+1)) d ≤ 3 := by
      intro d
      have hd:=suffixOffset_lt _ d
      omega
    fin_cases j
    all_goals try (norm_num at hj)
    all_goals
      have hh:=actual_native_low_oriented_history reflected s R seed parent.localBase Mrow amp xi reserve b
        firstHeight budget parent.localBase_gt_one key hz1 hz2 firstIndex second eps units own w deleted q fees
        children hfirst Bsrc boxes sourceFacts (suffixOffset _) hn histories
      refine ⟨OrientedFamilyHistory.toNode parent F ?_⟩
      exact {
        word:=hh.word
        word_padding:=by
          intro d p k hk
          cases d with
          | none=>exact hh.word_padding none p k hk
          | some dc=>exact hh.word_padding (some dc) p k hk
        units:=hh.units
        code:=fun d p=>by
          cases d with
          | none=>exact hh.code none p
          | some dc=>exact hh.code (some dc) p
        injective:=by
          intro d p p' he
          apply hh.injective d
          cases d <;> exact he
        multiplier:=by
          intro d p
          cases d with
          | none=>exact hh.multiplier none p
          | some dc=>exact hh.multiplier (some dc) p
        missing:=by
          intro d p
          cases d with
          | none=>exact hh.missing none p
          | some dc=>exact hh.missing (some dc) p
        facts:=by
          intro d p
          cases d with
          | none=>exact hh.facts none p
          | some dc=>exact hh.facts (some dc) p }
  · intro d p
    apply Classical.choice
    change Nonempty (ActualPathTrace hH parent parent.unit F d p)
    fin_cases j
    all_goals try (norm_num at hj)
    all_goals
      cases d with
      | none=>
        refine ⟨?_⟩
        apply ActualPathTrace.terminal parent (by rfl) hm hA (by rfl) (by rfl) (by rfl)
          ampError hAmp0 hAmpFine
        exact hAmp
      | some dc=>
        rcases p with ⟨r,pc⟩
        let data:=paths r dc pc
        have hf:=selected_part_fields ((children r).part dc pc)
          (data.family.part dc data.childPrefix) data.multiplier data.part
        have bind : AttachedPathBinding (hH:=hH) parent data.child F data.family (some dc) ⟨r,pc⟩
            dc data.childPrefix data.edge := by
          refine {
            offset:=rfl
            terminal_scale:=hf.1
            terminal_length:=hf.2.1
            terminal_amp:=hf.2.2
            terminal_multiplier:=data.multiplier
            weight:=?_
            missing:=?_ }
          · exact congrArg₂ (fun a b : ℝ=>a*b) data.rawWeight data.weight
          · exact (mul_add parent.unit _ _).trans
              (congrArg₂ (fun a b : ℝ=>a+b) data.rawMissing.symm
                (congrArg (fun z : ℝ=>parent.unit*z) data.historyMissing))
        exact ⟨ActualPathTrace.prepend rfl data.trace data.edge bind⟩
  · intro d p
    fin_cases j
    all_goals try (norm_num at hj)
    all_goals
      cases d with
      | none=>exact ownLoss
      | some dc=>exact childrenLoss p.1 dc p.2
  · intro d p
    fin_cases j
    all_goals try (norm_num at hj)
    all_goals
      cases d with
      | none=>exact ownSource
      | some dc=>exact childrenSource p.1 dc p.2
  · intro d p b
    fin_cases j
    all_goals try (norm_num at hj)
    all_goals
      cases d with
      | none=>exact ownClass b
      | some dc=>exact childrenClass p.1 dc p.2 b

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_selected_receipt
