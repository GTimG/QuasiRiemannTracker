/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSelectedReceipt
import Candidate.Research.RecursiveAffine.ActualChildHistory
import Candidate.Research.RecursiveAffine.ActualChildTerminalFacts

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
variable {C : SourceContext (α:=alpha) M H}
variable (reflected second : Bool)(s : Input alpha)(R seed : Ideal O)
variable (Mrow amp xi reserve eps b firstHeight : ℝ)(budget : ℕ)
variable (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (C.globalBase^Mrow)
  C.globalBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
local notation "Rows"=>NativeLowRows reflected s R seed C.globalBase Mrow amp xi reserve b firstHeight
  budget C.globalBase_gt_one key hz1 hz2 firstIndex
local notation "first"=>fun l=>geometryFirstLabel s R seed (C.globalBase^Mrow) C.globalBase xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val
local notation "rowKey"=>nativeLowHistoryCode reflected s R seed C.globalBase Mrow amp xi reserve b firstHeight
  budget C.globalBase_gt_one key hz1 hz2 firstIndex

/-- The actual child output uses the one fixed physical source cap and
one global dyad box family. These are exact choices of the finite source
schedule, not assumed bounds on the selected forest. -/
structure NativeRootSelectedSource
    (units : FirstSourceLabel→O)(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1))
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(r : Rows) where
  data : NativeRootSelectedChild reflected second s R seed Mrow amp xi reserve eps b firstHeight
    budget key hz1 hz2 firstIndex units w deleted q fees children r
  sourceCap : data.Bsrc=Bsrc
  sourceBoxes : data.boxes=fun k=>boxes (k+1)

/-- Construct the entire root LOW arithmetic receipt from actual source
choices and genuine strictly deeper outputs. All chronology, terminal
source caps, class licences and loss bounds are derived from those SAME
outputs. There is no separate daughter-history/cap/path/payment premise. -/
def actual_native_root_source_receipt
    (units : FirstSourceLabel→O)(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1))
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(hBsrc : 0 ≤ Bsrc)
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
    (sourceFacts : ∀r : Rows,DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
      C.globalBase Bsrc (boxes 0) ((),rowKey r))
    (sources : ∀r,children r=emptyReturnedForest ∨ Nonempty (NativeRootSelectedSource reflected second
      s R seed Mrow amp xi reserve eps b firstHeight budget key hz1 hz2 firstIndex
      units w deleted q fees children Bsrc boxes r)) :
    NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes := by
  apply actual_native_root_selected_receipt reflected second s R seed Mrow amp xi reserve eps b firstHeight
    budget key hz1 hz2 firstIndex units w deleted q fees children Bsrc boxes hfirst sourceFacts
  · intro r
    apply Classical.choice
    rcases sources r with hz | hs
    · rw [hz]
      exact ⟨OrientedFamilyHistory.empty _ _ _⟩
    · let chosen:=Classical.choice hs
      let data:=chosen.data
      have hcap : 0 ≤ data.Bsrc := by rw [chosen.sourceCap];exact hBsrc
      have hh:=data.output.globalHistory hcap _ data.root
      rw [data.family]
      let F:=data.output.globalFamilyAtRoot _ data.root
      have hh' : OrientedFamilyHistory F (suffixOffset 4) Bsrc data.boxes :=
        Eq.mp (congrArg (fun cap=>OrientedFamilyHistory F (suffixOffset 4) cap data.boxes)
          (show data.Bsrc=Bsrc from chosen.sourceCap)) hh
      exact ⟨Eq.mp (congrArg (fun bs=>OrientedFamilyHistory F (suffixOffset 4) Bsrc bs)
        (show data.boxes=(fun k=>boxes (k+1)) from chosen.sourceBoxes)) hh'⟩
  · intro r
    rcases sources r with hz | hs
    · exact Or.inl hz
    · exact Or.inr ⟨(Classical.choice hs).data⟩
  · intro r d p
    rcases sources r with hz | hs
    · have hp : (children r).Prefix d→False := by rw [hz];exact fun p=>nomatch p
      exact False.elim (hp p)
    · let data:=(Classical.choice hs).data
      have hf:=data.output.globalTerminalFacts _ data.root
      rw [←data.family] at hf
      exact (hf.loss d p).trans (by norm_num [terminalLossCap])
  · intro r d p
    rcases sources r with hz | hs
    · have hp : (children r).Prefix d→False := by rw [hz];exact fun p=>nomatch p
      exact False.elim (hp p)
    · let data:=(Classical.choice hs).data
      have hf:=data.output.globalTerminalFacts _ data.root
      rw [←data.family] at hf
      exact hf.source d p
  · intro r d p b
    rcases sources r with hz | hs
    · have hp : (children r).Prefix d→False := by rw [hz];exact fun p=>nomatch p
      exact False.elim (hp p)
    · let data:=(Classical.choice hs).data
      have hf:=data.output.globalTerminalFacts _ data.root
      rw [←data.family] at hf
      exact hf.classCap d p b

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_root_source_receipt
