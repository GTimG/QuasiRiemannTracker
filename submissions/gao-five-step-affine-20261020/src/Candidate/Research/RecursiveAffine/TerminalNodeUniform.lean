/- A genuine uniform terminal base case for the finite source recursion.
Copyright (c) 2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.TerminalNativeApply

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153TerminalSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentNaturalFixedRaySource QuadraticInitialBound
open Cycle63InitialMass Cycle153Reachable Cycle153RegionalLow Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153.RegionalSchedule
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}

/-- Enlarging only the fixed scalar metadata retains the SAME actual
forest, literal history, physical path and every terminal source receipt. -/
def enlargeActualNodeOutput
    {C : SourceContext (α:=alpha) M H}{j : Fin 4}{N : ReachableNode C j}
    {constant constant' epsilon Bsrc : ℝ}{control control' : Finset (ℕ×ℕ)}
    {degree degree' : ℕ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH N constant epsilon Bsrc control degree boxes)
    (hconstant0 : 0 ≤ constant)(hconstant : constant ≤ constant')
    (hcontrol : control⊆control')(hdegree : degree ≤ degree') :
    NodeOutput hH N constant' epsilon Bsrc control' degree' boxes where
  family:=out.family
  chronology:=out.chronology
  path:=out.path
  terminalLoss:=out.terminalLoss
  terminalSource:=out.terminalSource
  classCap:=out.classCap
  energy:=by
    apply out.energy.trans
    apply terminal_factor_upgrade hconstant0 hconstant (diagonalControl_nonneg N.state.radial.profile)
      (N.profiles.control_nonneg control) (Cycle63Physical.profile_control_mono N.profiles hcontrol)
      (by have hh:=abs_nonneg N.t;linarith only [hh,N.height_nonneg]) hdegree
    exact add_nonneg (Real.rpow_nonneg (zero_lt_one.trans N.localBase_gt_one).le _)
      (out.family.value_nonneg (zero_lt_one.trans N.localBase_gt_one).le)

/-- The terminal base case is now produced from the native sources, with
one class cap, one profile control, one degree, one constant and one global
threshold chosen BEFORE the moving context and actual reachable node.
No energy, HIGH, LOW, AtState, counting or IH premise is assumed. -/
theorem eventual_actual_terminal_node_outputs
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta ≤ 7/8)
    (eps tau B Bsrc : ℝ)(heps : 0<eps)(htau : 0<tau)
    (eta : Character)(Q : Ideal O)(hQM : Q ≤ M)
    (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
    (hQ72 : internalQ Q eta ≤ Ideal.span {(72:O)})(boxes : ℕ→Finset (Fin 4→ℤ)) :
    ∃Kclass constant : ℝ,1 ≤ Kclass ∧ 0 < constant ∧
    ∃(control : Finset (ℕ×ℕ))(degree : ℕ),∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H),C.W=W→C.etaSeed=eta→C.Q=Q→C.globalBase=Z→
      C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→C.Bnorm=B→
      C.Tz=Z^tau→Kclass ≤ C.highClassCap→
    ∀N : ReachableNode C (3:Fin 4),
      Nonempty (NodeOutput hH N constant (oldLoss eps) Bsrc control degree boxes) := by
  letI : Fintype TerminalGridIndex:=Fintype.ofFinite _
  let schedule : (i : TerminalGridIndex)→TerminalNativeSchedule (alpha:=alpha)
      hH W hW hWs hbeta hbetaHi eps tau B heps eta Q hQM hQ72 i :=fun i=>
    Classical.choice (terminal_native_schedule_exists (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps htau eta Q hQM hQ0 hQt hQ72 i)
  let Kclass : ℝ:=uniformConstant (fun i=>(schedule i).Kclass)
  let constant : ℝ:=uniformConstant (fun i=>(schedule i).constant)
  let control : Finset (ℕ×ℕ):=uniformControl (fun i=>(schedule i).control)
  let degree : ℕ:=uniformDegree (fun i=>(schedule i).degree)
  have hclass:=uniformConstant_bounds (fun i=>(schedule i).Kclass)
  have hconstant:=uniformConstant_bounds (fun i=>(schedule i).constant)
  have hlocal : ∀ᶠY : ℝ in atTop,∀i,(schedule i).SourceAt Y :=
    Filter.eventually_all.2 (fun i=>(schedule i).eventually_sourceAt)
  have hglobal:=eventually_all_rebased_sources _ hlocal
  refine ⟨Kclass,constant,hclass.1,by linarith only [hconstant.1],control,degree,?_⟩
  filter_upwards [hglobal] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro C hCW hCeta hCQ hbase hgrid hmesh hB hheight hCclass N
  obtain ⟨i,hi⟩:=terminal_node_ledger_mem_family N hgrid
  have hsource : (schedule i).SourceAt N.localBase := by
    have hh:=hZ.2 N.unit N.unit_floor i
    rw [←hbase,←N.localBase_eq] at hh
    exact hh
  have hheight' : C.Tz=C.globalBase^tau := by rw [hbase];exact hheight
  obtain ⟨out⟩:=(schedule i).actual_node_output N hgrid hCW hCeta hCQ hmesh hB htau hheight' hi
    ((hclass.2 i).trans hCclass) Bsrc boxes hsource
  exact ⟨enlargeActualNodeOutput out (schedule i).constant_pos.le (hconstant.2 i)
    (control_subset_uniform (fun i=>(schedule i).control) i)
    (degree_le_uniform (fun i=>(schedule i).degree) i)⟩

end
end OAI.SevenEighths.Cycle153TerminalSchedule
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.eventual_actual_terminal_node_outputs
