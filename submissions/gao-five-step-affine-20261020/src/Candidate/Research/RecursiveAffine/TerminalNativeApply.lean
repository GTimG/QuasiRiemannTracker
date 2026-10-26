/- Actual terminal sources applied to literal reachable nodes.
Copyright (c) 2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.TerminalNativeSchedule
import Candidate.Research.RecursiveAffine.SourceContextHeight

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153TerminalSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentNaturalFixedRaySource Cycle63InitialMass
open Cycle153Reachable Cycle153RegionalLow Cycle153RegionalState
open Cycle153RecursiveHighProvider Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153.RegionalSchedule
attribute [local irreducible] GeometryAffineLowSelectedSpec RegionalAtState ActualHighNodeAt
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {W : ℝ→ℂ}{hW : ContDiff ℝ ∞ W}{hWs : Function.support W⊆Set.Icc (1:ℝ) 2}
variable {hbeta : 51/100 ≤ HeckeZeroSupremum.beta}{hbetaHi : HeckeZeroSupremum.beta ≤ 7/8}
variable {eps tau B : ℝ}{heps : 0<eps}{eta : Character}{Q : Ideal O}{hQM : Q ≤ M}
variable {hQ72 : internalQ Q eta ≤ Ideal.span {(72:O)}}{i : TerminalGridIndex}

namespace TerminalNativeSchedule

def SourceAt (s : TerminalNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
    eps tau B heps eta Q hQM hQ72 i) (Z : ℝ) : Prop :=
  1<Z ∧ 2<Z^s.g.τ ∧
  (letI : Cycle63.AffineLedger:=terminalLedger i;
    RegionalAtState (α:=alpha) M H hH W hW hWs hbeta hbetaHi s.g 2 20
      (localSlotMesh eps) (oldLoss eps) (by norm_num) s.Psi s.SH s.dh s.degree s.control s.Cenergy s.Chigh s.Cs
      s.Sp s.degreeLow s.Klow (by norm_num) (localSlotMesh_pos heps).le eta Q hQM hQ72 Z) ∧
  (∀J,TerminalLowSourceAt hH W hbeta s.g s.Cs eta Q hQM hQ72 i J
    (s.Sp J) (s.degreeLow J) (s.Klow J) Z) ∧
  (letI : Cycle63.AffineLedger:=terminalLedger i;
    ActualHighNodeAt (base:=prefixDictionary 3) (α:=alpha) M H hH W hW hWs hbeta hbetaHi
      s.g (1/4) (9/4) 2 20 (localSlotMesh eps) (oldLoss eps) tau B
      (highSourceLossNeeded primitiveError (Fintype.card alpha)) (by norm_num)
      s.Psi s.SH s.dh s.Kclass s.Kh eta Q hQM hQ72 Z)

theorem eventually_sourceAt (s : TerminalNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
    eps tau B heps eta Q hQM hQ72 i) : ∀ᶠZ : ℝ in atTop,s.SourceAt Z := by
  filter_upwards [s.actualAtState,s.actualLow,s.actualHigh,eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop s.g.τ_pos).eventually (eventually_gt_atTop (2:ℝ))] with Z ha hl hh hz ht
  exact ⟨hz,ht,ha,hl,hh⟩

def constant (s : TerminalNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
    eps tau B heps eta Q hQM hQ72 i) : ℝ :=s.Cenergy*(1+s.Chigh*(2*s.Kh))

theorem constant_pos (s : TerminalNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
    eps tau B heps eta Q hQM hQ72 i) : 0 < s.constant := by
  have hp : 0 ≤ s.Chigh*(2*s.Kh) := mul_nonneg s.Chigh_nonnegative (by linarith only [s.Kh_nonnegative])
  exact mul_pos s.Cenergy_positive (by linarith only [hp])

/-- The native reserve, rather than a source-specific lower amplifier
assumption, pays the real AtState driver exponent at every cell. -/
theorem amplifier_paid (s : TerminalNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
    eps tau B heps eta Q hQM hQ72 i) {cell : ℝ}
    (hc : letI : Cycle63.AffineLedger:=terminalLedger i;
      Cycle63.AffineLedger.firstCellTop ≤ cell ∧ cell ≤ Cycle63.AffineLedger.slotTop) :
    letI : Cycle63.AffineLedger:=terminalLedger i;
      3*s.g.δ ≤ Cycle63.AffineLedger.amp cell := by
  letI : Cycle63.AffineLedger:=terminalLedger i
  have hr:=regional_native_reserve (4:Fin 5) i
  have hf:=@native_reserve_lt_half_amplifier (terminalLedger i)
  have ha:=Cycle63.AffineLedger.amp_bounds hc
  have hd:=(nativeDriverRate_budgets (Fintype.card alpha)).2.1
  rw [s.delta]
  have hm:=nativeMu_pos
  have hp : 128*nativeMu < Cycle63.AffineLedger.amp cell/2 :=
    hr.trans_lt (hf.trans_le (div_le_div_of_nonneg_right ha.1 (by norm_num)))
  linarith only [hp,hd,hm]

/-- Apply the prechosen actual source package to the same moving node.
The selected ledger index comes from the genuine terminal geometry;
Tz stays the original height, using its exact local exponent tau/unit. -/
theorem actual_node_output
    (s : TerminalNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps eta Q hQM hQ72 i)
    {C : SourceContext (α:=alpha) M H}(N : ReachableNode C (3:Fin 4))
    (hgrid : C.gridDenominator=gridSize)(hCW : C.W=W)(hCeta : C.etaSeed=eta)(hCQ : C.Q=Q)
    (hmesh : C.slotMesh=localSlotMesh eps)(hB : C.Bnorm=B)
    (htau : 0<tau)(hheight : C.Tz=C.globalBase^tau)
    (hledger : terminalLedger i=N.ledger)(hclass : s.Kclass ≤ C.highClassCap)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(hs : s.SourceAt N.localBase) :
    Nonempty (NodeOutput hH N s.constant (oldLoss eps) Bsrc s.control s.degree boxes) := by
  letI : Cycle63.AffineLedger:=N.ledger
  have hAt : RegionalAtState (α:=alpha) M H hH C.W C.W_smooth C.W_support hbeta hbetaHi
      s.g 2 20 C.slotMesh (oldLoss eps) (by norm_num) s.Psi s.SH s.dh s.degree s.control s.Cenergy s.Chigh s.Cs
      s.Sp s.degreeLow s.Klow (by norm_num) C.slotMesh_pos.le C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase := by
    have hh:=hs.2.2.1
    rw [hledger] at hh
    simpa only [←hCW,←hCeta,←hCQ,←hmesh] using hh
  have hclosed : GeometryAffineLowSelectedSpec (α:=N.slots) M H hH C.W hbeta s.g 2
      (Cycle25.Energy.commonMesh 2 28 1 (s.g.μ/8)) s.Cs (fun _ _ _=>True)
      (fun _ _ _ _ _=>True) (s.Sp N.slots) (s.degreeLow N.slots) (s.Klow N.slots)
      C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase := by
    have hh:=hs.2.2.2.1 N.slots
    dsimp only [TerminalLowSourceAt] at hh
    have hledgerRaw : Cycle153.regionalFamily Cycle153.FixedStages.stage4 gridSize i=N.ledger :=hledger
    rw [hledgerRaw] at hh
    have hdec : (Classical.decEq (↥N.slots):DecidableEq (↥N.slots))=(inferInstance:DecidableEq (↥N.slots)) := Subsingleton.elim _ _
    rw [hdec] at hh
    simpa only [←hCW,←hCeta,←hCQ] using hh
  have hhigh : ActualHighNodeAt (base:=prefixDictionary 3) (α:=alpha) M H hH C.W C.W_smooth C.W_support
      hbeta hbetaHi s.g (1/4) (9/4) 2 20 C.slotMesh (oldLoss eps) tau C.Bnorm
      (highSourceLossNeeded primitiveError (Fintype.card alpha)) (by norm_num)
      s.Psi s.SH s.dh s.Kclass s.Kh C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase := by
    have hh:=hs.2.2.2.2
    rw [hledger] at hh
    simpa only [←hCW,←hCeta,←hCQ,←hmesh,←hB] using hh
  have hheight' : C.Tz=N.localBase^(tau/N.unit) := by
    rw [hheight,N.localBase_eq,source_zero_height_rebase C.globalBase_gt_one N.unit_pos]
  have hcell:=Cycle63.AffineLedger.cellUpper_bounds
    ((Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩).1)
    ((Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩).2.1)
  have hamp : 3*s.g.δ ≤ Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j : N.slots,C.originalWeight j/N.unit))) := by
    have hh:=s.amplifier_paid (by rw [hledger];exact hcell)
    rw [hledger] at hh
    exact hh
  exact actual_terminal_node_output hH N hgrid hbeta hbetaHi s.g (oldLoss eps) tau
    (highSourceLossNeeded primitiveError (Fintype.card alpha)) (tau/N.unit)
    s.Psi s.SH s.dh s.degree s.control s.Cenergy s.Chigh s.Cs s.Kh s.Kclass Bsrc boxes
    s.Sp s.degreeLow s.Klow hs.2.1 s.Cenergy_positive.le s.Chigh_nonnegative s.Kh_nonnegative hclass
    (terminal_native_loss_bound heps) (local_presentation_height N.unit_pos N.unit_le_one htau.le le_rfl)
    hheight' hAt hclosed hhigh hamp

end TerminalNativeSchedule
end
end OAI.SevenEighths.Cycle153TerminalSchedule
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.TerminalNativeSchedule.actual_node_output
