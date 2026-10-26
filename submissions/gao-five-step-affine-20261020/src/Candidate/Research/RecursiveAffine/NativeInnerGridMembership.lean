/- Finite ledger selection for every actual inner node, before moving heights.
Copyright (c)2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.InnerNativeSchedule
import Candidate.Research.RecursiveAffine.NativeTerminalUniform

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
namespace Cycle153
noncomputable section

/-- A rounded plane majorant need not equal the physical source plane.
Bounds on the actual lengths suffice to retain the same finite grid. -/
theorem exists_gridPosition_from_length_bounds
    {S : RegionalStage}{N : ℕ}{B n₁ n₂ z : ℝ}
    (hN : 0<N)(hz : 0≤z)(hB0 : 0≤B)(h₁ : 0≤n₁)(h₂ : 0≤n₂)
    (hs : n₁+n₂≤1)(h : (roundedPosition (1/N) B n₁ n₂ z).Facts S) :
    ∃i : GridCoordinates N,gridPosition N i=roundedPosition (1/N) B n₁ n₂ z :=by
  have hg : (0:ℝ)<1/N :=by
    have hn : (0:ℝ)<N :=by exact_mod_cast hN
    positivity
  have hB : B≤1 :=(roundUp_bounds hg _).1.trans h.B_le_one
  have hzz : z≤1 :=(roundUp_bounds hg _).1.trans h.slotTop_le_one
  have hm0 : 0 ≤ min n₁ n₂ :=le_min h₁ h₂
  have hm : min n₁ n₂≤1 :=(min_le_left _ _).trans (by linarith only [hs,h₂])
  have hs0 : 0≤n₁+n₂ :=add_nonneg h₁ h₂
  refine ⟨(⟨_,Nat.lt_succ_of_le (coordinate_le hB).1⟩,
    ⟨_,Nat.lt_succ_of_le (coordinate_le hzz).1⟩,
    ⟨_,Nat.lt_succ_of_le (coordinate_le hm).2⟩,
    ⟨_,Nat.lt_succ_of_le (coordinate_le hs).2⟩),?_⟩
  simp only [gridPosition,roundedPosition,roundUp_eq_coordinate hB0,
    roundUp_eq_coordinate hz,roundDown_eq_coordinate hm0,roundDown_eq_coordinate hs0]

end
end Cycle153

namespace OAI.SevenEighths.Cycle153TerminalSchedule
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentNaturalFixedRaySource CenteredMomentEnergyBands
open Cycle153Reachable Cycle153SourceSchedule Cycle153.RegionalSchedule
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- The actual plain window forces its rounded intercept to be positive.
This proves positivity for all nodes without identifying a source length
with a majorant or postulating a physical-coordinate inequality. -/
theorem actual_inner_node_plane_pos (N : ReachableNode C j) : 0<N.plane :=by
  letI : Cycle63.AffineLedger:=N.ledger
  have hg : (0:ℝ)<1/C.gridDenominator :=by
    have hn : (0:ℝ)<C.gridDenominator :=by exact_mod_cast C.grid_positive
    positivity
  have hz : 0≤∑i : N.slots,C.originalWeight i/N.unit :=
    Finset.sum_nonneg (fun i _=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
  have h₁ :=N.positionFacts.windowBottom_pos.trans_le N.window.left_ge
  have h₂ :=N.positionFacts.windowBottom_pos.trans_le N.window.right_ge
  have hprod : 0≤(innerStage j.val).lam*(∑i : N.slots,C.originalWeight i/N.unit) :=
    mul_nonneg (by linarith only [(innerStage j.val).one_le_lam]) hz
  have hw : length N.localBase N.X1+length N.localBase N.X2+
      (innerStage j.val).lam*(∑i : N.slots,C.originalWeight i/N.unit)≤N.position.B :=N.window.plane
  have hp : 0<N.position.B :=lt_of_lt_of_le (by linarith only [h₁,h₂,hprod]) hw
  have hB : N.position.B=Cycle153.roundUp (1/C.gridDenominator) N.plane :=
    congrArg Cycle153.RegionalPosition.B N.rounded
  rw [hB] at hp
  by_contra hn
  have hd : N.plane/(1/C.gridDenominator)≤0 :=
    div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hg.le
  have hc : ⌈N.plane/(1/C.gridDenominator)⌉≤(0:ℤ) :=
    Int.ceil_le.mpr (by simpa only [Int.cast_zero] using hd)
  have hc' : (⌈N.plane/(1/C.gridDenominator)⌉:ℝ)≤0 :=by exact_mod_cast hc
  have hh : Cycle153.roundUp (1/C.gridDenominator) N.plane≤0 :=
    mul_nonpos_of_nonpos_of_nonneg hc' hg.le
  exact (not_lt_of_ge hh) hp

/-- All actual intermediate and terminal nodes select a prechosen finite
native ledger. The proof retains the real rounded majorant; it adds no
source-plane, energy, HIGH, LOW or induction hypothesis. -/
theorem actual_inner_node_ledger_mem_family (N : ReachableNode C j)
    (hgrid : C.gridDenominator=gridSize) :
    ∃i : InnerGridIndex j,innerLedger j i=N.ledger :=by
  letI : Cycle63.AffineLedger:=N.ledger
  have hz : 0≤∑i : N.slots,C.originalWeight i/N.unit :=
    Finset.sum_nonneg (fun i _=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
  have h₁ :=N.positionFacts.windowBottom_pos.trans_le N.window.left_ge
  have h₂ :=N.positionFacts.windowBottom_pos.trans_le N.window.right_ge
  have hprod : 0≤(innerStage j.val).lam*(∑i : N.slots,C.originalWeight i/N.unit) :=
    mul_nonneg (by linarith only [(innerStage j.val).one_le_lam]) hz
  have hs : length N.localBase N.X1+length N.localBase N.X2≤1 :=by
    have hp : length N.localBase N.X1+length N.localBase N.X2+
        (innerStage j.val).lam*(∑i : N.slots,C.originalWeight i/N.unit)≤N.position.B :=N.window.plane
    have hb:=N.positionFacts.B_le_one
    linarith only [hp,hb,hprod]
  have hFacts : (Cycle153.roundedPosition (1/(gridSize:ℝ)) N.plane
      (length N.localBase N.X1) (length N.localBase N.X2)
      (∑i : N.slots,C.originalWeight i/N.unit)).Facts (innerStage j.val) :=by
    rw [←hgrid,←N.rounded]
    exact N.positionFacts
  obtain ⟨i,hi⟩:=Cycle153.exists_gridPosition_from_length_bounds gridSize_pos hz
    (actual_inner_node_plane_pos N).le h₁.le h₂.le hs hFacts
  refine ⟨⟨i,hi ▸ hFacts⟩,?_⟩
  change Cycle153.regionalLedger _ (Cycle153.gridPosition gridSize i) _=N.ledger
  apply Cycle153.regionalLedger_congr
  exact hi.trans (by rw [←hgrid,←N.rounded])

end
end OAI.SevenEighths.Cycle153TerminalSchedule
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.actual_inner_node_plane_pos
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.actual_inner_node_ledger_mem_family
