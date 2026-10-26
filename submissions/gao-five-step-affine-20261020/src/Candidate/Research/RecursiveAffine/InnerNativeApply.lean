/- Apply the genuine inner native schedules to the same moving regional node.
Copyright (c)2026 Zhongpai Gao. Native operators by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.InnerNativeSchedule
import Candidate.Research.RecursiveAffine.NativeNodeOutput
import Candidate.Research.RecursiveAffine.SourceContextFactory

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
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {W : ℝ→ℂ}{hW : ContDiff ℝ ∞ W}{hWs : Function.support W⊆Set.Icc (1:ℝ) 2}
variable {hbeta : 51/100≤HeckeZeroSupremum.beta}{hbetaHi : HeckeZeroSupremum.beta≤7/8}
variable {eps tau B : ℝ}{heps : 0<eps}{eta : Character}{Q : Ideal O}{hQM : Q≤M}
variable {hQ72 : internalQ Q eta≤Ideal.span {(72:O)}}{j : Fin 4}{i : InnerGridIndex j}

namespace InnerNativeSchedule

/-- Every actual inner ledger has the same paid reserve. This is a
consequence of its fixed stage and native driver, not a source hypothesis. -/
theorem amplifier_paid
    (s : InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps eta Q hQM hQ72 j i) {cell : ℝ}
    (hc : letI : Cycle63.AffineLedger:=innerLedger j i;
      Cycle63.AffineLedger.firstCellTop≤cell ∧ cell≤Cycle63.AffineLedger.slotTop) :
    letI : Cycle63.AffineLedger:=innerLedger j i;
      3*s.g.δ≤Cycle63.AffineLedger.amp cell :=by
  letI : Cycle63.AffineLedger:=innerLedger j i
  have hr : 128*nativeMu≤Cycle63.AffineLedger.lowReserve :=by
    fin_cases j
    · exact regional_native_reserve (1:Fin 5) i
    · exact regional_native_reserve (2:Fin 5) i
    · exact regional_native_reserve (3:Fin 5) i
    · exact regional_native_reserve (4:Fin 5) i
  have hf:=@native_reserve_lt_half_amplifier (innerLedger j i)
  have ha:=Cycle63.AffineLedger.amp_bounds hc
  have hd:=(nativeDriverRate_budgets (Fintype.card alpha)).2.1
  rw [s.delta]
  have hm:=nativeMu_pos
  have hp : 128*nativeMu<Cycle63.AffineLedger.amp cell/2 :=
    hr.trans_lt (hf.trans_le (div_le_div_of_nonneg_right ha.1 (by norm_num)))
  linarith only [hp,hd,hm]

/-- The actual HIGH and AtState operators choose their constants and
height threshold before every moving context and node. The only remaining
analytic input is the literal whole RAW source, supplied by the recursive
LOW producer. Its receipt is the one retained in the output. This is an
application theorem, not an existence assertion for that RAW source. -/
theorem eventual_actual_node_output_from_raw_all_boxes
    (s : InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps eta Q hQM hQ72 j i)
    (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)
    (Klow : Finset alpha→ℝ)(hKlow : ∀J,0≤Klow J)
    (Kreturn Bsrc : ℝ)(hKreturn : 0≤Kreturn)(hBsrc : 0≤Bsrc)
    (hBnorm : B=returnedNormCap Bsrc)(htau : 0<tau)
    :
    ∃Cenergy Chigh : ℝ,0<Cenergy ∧ 0≤Chigh ∧
    ∃(degree : ℕ)(control : Finset (ℕ×ℕ)),∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(boxes : ℕ→Finset (Fin 4→ℤ))(C : SourceContext (α:=alpha) M H),C.W=W→C.etaSeed=eta→C.Q=Q→C.globalBase=Z→
      C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→C.Bnorm=B→
      C.Tz=Z^tau→s.Kclass≤C.highClassCap→
    ∀N : ReachableNode C j,innerLedger j i=N.ledger→
      (∀hT : 2<N.localBase^s.g.τ,
        letI : Cycle63.AffineLedger:=N.ledger;
        NativeNodeRawLowAt hH N hbeta s.g s.Cs Sp degreeLow Klow hT hbetaHi
          (N.state.rowWidth+3*s.g.δ-Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
            (Cycle63.AffineLedger.originalCell (∑k : N.slots,C.originalWeight k/N.unit)))+oldLoss eps)
          Kreturn Bsrc boxes)→
      Nonempty (NodeOutput hH N
        (Cenergy*(1+Chigh*(2*Kreturn+2*s.Kh))) (oldLoss eps) Bsrc control degree boxes) :=by
  obtain ⟨degree,control,hSH,hdh,Cenergy,Chigh,hCenergy,hChigh,hAt⟩:=
    s.actualAtState Sp degreeLow Klow hKlow
  let LocalAt :=fun Y : ℝ=>2≤Y ∧ 2<Y^s.g.τ ∧
    (letI : Cycle63.AffineLedger:=innerLedger j i;
      RegionalAtState (α:=alpha) M H hH W hW hWs hbeta hbetaHi s.g 2 20
        (localSlotMesh eps) (oldLoss eps) (by norm_num) s.Psi s.SH s.dh degree control Cenergy Chigh s.Cs
        Sp degreeLow Klow (by norm_num) (localSlotMesh_pos heps).le eta Q hQM hQ72 Y) ∧
    (letI : Cycle63.AffineLedger:=innerLedger j i;
      ActualHighNodeAt (base:=prefixDictionary j.val) (α:=alpha) M H hH W hW hWs hbeta hbetaHi
        s.g (1/4) (9/4) 2 20 (localSlotMesh eps) (oldLoss eps) tau B
        (highSourceLossNeeded primitiveError (Fintype.card alpha)) (by norm_num)
        s.Psi s.SH s.dh s.Kclass s.Kh eta Q hQM hQ72 Y)
  have hlocal : ∀ᶠY : ℝ in atTop,LocalAt Y :=by
    filter_upwards [hAt,s.actualHigh,eventually_ge_atTop (2:ℝ),
      (tendsto_rpow_atTop s.g.τ_pos).eventually (eventually_gt_atTop (2:ℝ))] with Y ha hh hY ht
    exact ⟨hY,ht,ha,hh⟩
  have hglobal:=eventually_all_rebased_sources LocalAt hlocal
  refine ⟨Cenergy,Chigh,hCenergy,hChigh,degree,control,?_⟩
  filter_upwards [hglobal] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro boxes C hCW hCeta hCQ hbase hgrid hmesh hB hheight hclass N hledger hraw
  letI : Cycle63.AffineLedger:=N.ledger
  have hs : LocalAt N.localBase :=by
    have hh:=hZ.2 N.unit N.unit_floor
    rw [←hbase,←N.localBase_eq] at hh
    exact hh
  have hAtNode : RegionalAtState (α:=alpha) M H hH C.W C.W_smooth C.W_support hbeta hbetaHi
      s.g 2 20 C.slotMesh (oldLoss eps) (by norm_num) s.Psi s.SH s.dh degree control Cenergy Chigh s.Cs
      Sp degreeLow Klow (by norm_num) C.slotMesh_pos.le C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase :=by
    have hh:=hs.2.2.1
    rw [hledger] at hh
    simpa only [←hCW,←hCeta,←hCQ,←hmesh] using hh
  have hHighNode : ActualHighNodeAt (base:=prefixDictionary j.val) (α:=alpha) M H hH
      C.W C.W_smooth C.W_support hbeta hbetaHi s.g (1/4) (9/4) 2 20 C.slotMesh (oldLoss eps) tau C.Bnorm
      (highSourceLossNeeded primitiveError (Fintype.card alpha)) (by norm_num)
      s.Psi s.SH s.dh s.Kclass s.Kh C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase :=by
    have hh:=hs.2.2.2
    rw [hledger] at hh
    simpa only [←hCW,←hCeta,←hCQ,←hmesh,←hB] using hh
  have hheight' : C.Tz=N.localBase^(tau/N.unit) :=by
    rw [hheight,←hbase,N.localBase_eq,source_zero_height_rebase C.globalBase_gt_one N.unit_pos]
  have hcell:=Cycle63.AffineLedger.cellUpper_bounds
    ((Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩).1)
    ((Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩).2.1)
  have hamp : 3*s.g.δ≤Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑k : N.slots,C.originalWeight k/N.unit))) :=by
    have hh:=s.amplifier_paid (by rw [hledger];exact hcell)
    rw [hledger] at hh
    exact hh
  have hcap : terminalLossCap (3:Fin 4)≤terminalLossCap j :=by
    have hj : (j.val:ℝ)≤3 :=by exact_mod_cast Nat.le_of_lt_succ j.isLt
    change (5-(3:ℝ))/1000000000000≤(5-(j.val:ℝ))/1000000000000
    linarith only [hj]
  have hloss : highSourceLossNeeded primitiveError (Fintype.card alpha)+oldLoss eps≤terminalLossCap j :=
    (terminal_native_loss_bound (alpha:=alpha) heps).trans hcap
  have hbudget : ∀d : SuffixDepth (4-j.val),(suffixOffset (4-j.val) d:ℝ)*Bsrc≤C.Bnorm :=by
    intro d
    rw [hB,hBnorm]
    exact suffix_source_budget hBsrc j d
  exact actual_node_output_from_raw_physical_source hH N hgrid hbeta hbetaHi
    s.g (oldLoss eps) tau (highSourceLossNeeded primitiveError (Fintype.card alpha)) (tau/N.unit)
    s.Psi s.SH s.dh degree control Cenergy Chigh s.Cs s.Kh s.Kclass Kreturn Bsrc boxes
    Sp degreeLow Klow hs.2.1 hCenergy.le hChigh s.Kh_nonnegative hKreturn hKlow
    hBsrc hbudget hs.1 hclass hloss
    (local_presentation_height N.unit_pos N.unit_le_one htau.le le_rfl)
    hheight' hAtNode hHighNode (hraw hs.2.1) hamp

/-- Fixed-box specialization of the uniform moving-box application. -/
theorem eventual_actual_node_output_from_raw
    (s : InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps eta Q hQM hQ72 j i)
    (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)
    (Klow : Finset alpha→ℝ)(hKlow : ∀J,0≤Klow J)
    (Kreturn Bsrc : ℝ)(hKreturn : 0≤Kreturn)(hBsrc : 0≤Bsrc)
    (hBnorm : B=returnedNormCap Bsrc)(htau : 0<tau)
    (boxes : ℕ→Finset (Fin 4→ℤ)) :
    ∃Cenergy Chigh : ℝ,0<Cenergy ∧ 0≤Chigh ∧
    ∃(degree : ℕ)(control : Finset (ℕ×ℕ)),∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H),C.W=W→C.etaSeed=eta→C.Q=Q→C.globalBase=Z→
      C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→C.Bnorm=B→
      C.Tz=Z^tau→s.Kclass≤C.highClassCap→
    ∀N : ReachableNode C j,innerLedger j i=N.ledger→
      (∀hT : 2<N.localBase^s.g.τ,
        letI : Cycle63.AffineLedger:=N.ledger;
        NativeNodeRawLowAt hH N hbeta s.g s.Cs Sp degreeLow Klow hT hbetaHi
          (N.state.rowWidth+3*s.g.δ-Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
            (Cycle63.AffineLedger.originalCell (∑k : N.slots,C.originalWeight k/N.unit)))+oldLoss eps)
          Kreturn Bsrc boxes)→
      Nonempty (NodeOutput hH N
        (Cenergy*(1+Chigh*(2*Kreturn+2*s.Kh))) (oldLoss eps) Bsrc control degree boxes) :=by
  obtain ⟨Cenergy,Chigh,hCenergy,hChigh,degree,control,hout⟩:=
    s.eventual_actual_node_output_from_raw_all_boxes Sp degreeLow Klow hKlow
      Kreturn Bsrc hKreturn hBsrc hBnorm htau
  refine ⟨Cenergy,Chigh,hCenergy,hChigh,degree,control,?_⟩
  filter_upwards [hout] with Z hZ
  exact ⟨hZ.1,hZ.2 boxes⟩

end InnerNativeSchedule
end
end OAI.SevenEighths.Cycle153TerminalSchedule
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.InnerNativeSchedule.amplifier_paid
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.InnerNativeSchedule.eventual_actual_node_output_from_raw

#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.InnerNativeSchedule.eventual_actual_node_output_from_raw_all_boxes
