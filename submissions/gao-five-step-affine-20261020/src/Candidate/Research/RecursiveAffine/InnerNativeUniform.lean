/- Uniform native inner operators at every actual ledger and moving dyad box.
Copyright (c)2026 Zhongpai Gao. Native estimates by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.InnerNativeApply
import Candidate.Research.RecursiveAffine.NativeInnerGridMembership
import Candidate.Research.RecursiveAffine.TerminalNodeUniform

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153TerminalSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentNaturalFixedRaySource Cycle63InitialMass
open Cycle153Reachable Cycle153RegionalLow Cycle153RegionalState
open Cycle153RecursiveHighProvider Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153.RegionalSchedule
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}

/-- All native operators and constants are fixed before the global base,
boxes, context and node. The finite ledger is selected from the actual
window. The remaining source premise is the literal RAW predicate at that
same node and schedule; this theorem does not assert RAW existence. -/
theorem eventual_actual_inner_node_outputs_from_raw_all_boxes
    (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (eps tau B Bsrc : ℝ)(heps : 0<eps)(htau : 0<tau)(hBsrc : 0≤Bsrc)
    (hBnorm : B=returnedNormCap Bsrc)
    (eta : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q eta≤Ideal.span {(72:O)})
    (j : Fin 4)
    (S : ∀i : InnerGridIndex j,InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps eta Q hQM hQ72 j i)
    (Sp : InnerGridIndex j→Finset alpha→Finset (ℕ×ℕ))
    (degreeLow : InnerGridIndex j→Finset alpha→ℕ)
    (Klow : InnerGridIndex j→Finset alpha→ℝ)(hKlow : ∀i J,0≤Klow i J)
    (Kreturn : ℝ)(hKreturn : 0≤Kreturn) :
    ∃Kclass constant : ℝ,1≤Kclass ∧ 0<constant ∧
    ∃(control : Finset (ℕ×ℕ))(degree : ℕ),∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(boxes : ℕ→Finset (Fin 4→ℤ))(C : SourceContext (α:=alpha) M H),C.W=W→C.etaSeed=eta→C.Q=Q→
      C.globalBase=Z→C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→C.Bnorm=B→
      C.Tz=Z^tau→Kclass≤C.highClassCap→
    ∀N : ReachableNode C j,
      (∀i : InnerGridIndex j,innerLedger j i=N.ledger→∀hT : 2<N.localBase^(S i).g.τ,
        letI : Cycle63.AffineLedger:=N.ledger;
        NativeNodeRawLowAt hH N hbeta (S i).g (S i).Cs (Sp i) (degreeLow i) (Klow i) hT hbetaHi
          (N.state.rowWidth+3*(S i).g.δ-Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
            (Cycle63.AffineLedger.originalCell (∑k : N.slots,C.originalWeight k/N.unit)))+oldLoss eps)
          Kreturn Bsrc boxes)→
      Nonempty (NodeOutput hH N constant (oldLoss eps) Bsrc control degree boxes) :=by
  letI : Fintype (InnerGridIndex j):=Fintype.ofFinite _
  have produce:=fun i : InnerGridIndex j=>
    (S i).eventual_actual_node_output_from_raw_all_boxes (Sp i) (degreeLow i) (Klow i) (hKlow i)
      Kreturn Bsrc hKreturn hBsrc hBnorm htau
  choose Ce Ch hCe hCh degreeAt controlAt hAt using produce
  let constantAt:=fun i : InnerGridIndex j=>Ce i*(1+Ch i*(2*Kreturn+2*(S i).Kh))
  have hpos : ∀i,0<constantAt i :=by
    intro i
    dsimp only [constantAt]
    have hh:=(S i).Kh_nonnegative
    have hc:=hCh i
    have he:=hCe i
    positivity
  let Kclass:=uniformConstant (fun i=>(S i).Kclass)
  let constant:=uniformConstant constantAt
  let control:=uniformControl controlAt
  let degree:=uniformDegree degreeAt
  have hclass:=uniformConstant_bounds (fun i=>(S i).Kclass)
  have hconstant:=uniformConstant_bounds constantAt
  have hglobal:=Filter.eventually_all.mpr hAt
  refine ⟨Kclass,constant,hclass.1,by linarith only [hconstant.1],control,degree,?_⟩
  filter_upwards [hglobal,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro boxes C hCW hCeta hCQ hbase hgrid hmesh hB hheight hCclass N hraw
  obtain ⟨i,hi⟩:=actual_inner_node_ledger_mem_family N hgrid
  obtain ⟨out⟩:=(hZ i).2 boxes C hCW hCeta hCQ hbase hgrid hmesh hB hheight
    ((hclass.2 i).trans hCclass) N hi (hraw i hi)
  exact ⟨enlargeActualNodeOutput out (hpos i).le (hconstant.2 i)
    (control_subset_uniform controlAt i) (degree_le_uniform degreeAt i)⟩

end
end OAI.SevenEighths.Cycle153TerminalSchedule
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.eventual_actual_inner_node_outputs_from_raw_all_boxes
