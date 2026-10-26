/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeDirectRoom
import Candidate.Research.RecursiveAffine.NativeRootDirectRoom

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153Geometry Cycle153ReachableGeometry Cycle63.Optimization

/-- All finite errors of the actual direct branch are paid by its true
room, including both copies of the width-loss bound. -/
theorem direct_certificate_from_room {r gbar a L mu deltaMax sourcePad omegaMax : ℝ}
    (hr0 : 0≤r) (hr1 : r≤1)
    (hroom : (1/1000000000:ℝ)≤r*((1-2*mu)-gbar)+a*(1-12*r)-L)
    (hsmall : deltaMax+sourcePad+2*omegaMax≤1/1000000000) :
    (r*(gbar+6*a)-a)+L+r*(deltaMax+sourcePad)+2*r*omegaMax≤
      r*(1-6*a-2*mu) := by
  have he:=mul_le_mul_of_nonneg_left hsmall hr0
  have hr:=mul_le_mul_of_nonneg_right hr1 (by norm_num : (0:ℝ)≤1/1000000000)
  nlinarith only [he,hr,hroom]

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

theorem nodeSourceOldGap_eq_native (N : ReachableNode C j) :
    letI : Cycle63.AffineLedger:=N.ledger
    Cycle63.AffineLedger.g (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))=
      (innerStage j.val).oldGap N.position := by
  letI : Cycle63.AffineLedger:=N.ledger
  rw [regional_actual_cell N.positionFacts ⟨N.window.slots_ge,N.window.slots_le⟩]
  rfl

/-- The certificate consumed by native direct_branch_facts, at the SAME
source-selected rounded cell and actual amplifier. No child-energy or
capacity estimate is a premise. -/
theorem actual_inner_direct_certificate (N : ReachableNode C j) (hj : j.val<3)
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin)
    (deltaMax sourcePad omegaMax : ℝ)
    (hsmall : deltaMax+sourcePad+2*omegaMax≤1/1000000000) :
    letI : Cycle63.AffineLedger:=N.ledger
    let b:=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit))
    (directNodeRate j*(Cycle63.AffineLedger.g b+6*Cycle63.AffineLedger.amp b)-
        Cycle63.AffineLedger.amp b)+Cycle63.AffineLedger.lowReserve+
      directNodeRate j*(deltaMax+sourcePad)+2*directNodeRate j*omegaMax≤
      directNodeRate j*(1-6*Cycle63.AffineLedger.amp b-2*Coordinates.mu) := by
  letI : Cycle63.AffineLedger:=N.ledger
  dsimp only
  rw [nodeSourceOldGap_eq_native N,nodeSourceAmp_eq_native N]
  have hr : 0≤directNodeRate j ∧ directNodeRate j≤1 := by
    fin_cases j <;> norm_num [directNodeRate,innerStage,Cycle153.FixedStages.stage1,
      Cycle153.FixedStages.stage2,Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4,
      slotPrice,betaBound,Coordinates.q1,Coordinates.q2,Coordinates.q3,Coordinates.q4]
  exact direct_certificate_from_room hr.1 hr.2 (native_node_direct_room N hj hgrid) hsmall

noncomputable local instance directRootLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
local instance directRootBinding : Cycle153.MarkedRootPrice.RootLedgerBinding directRootLedger:=
  Cycle153.MarkedRootPrice.fixedRootLedgerBinding

/-- Root direct deletion uses the original cell and root ledger. In
particular it does not substitute a fictitious first-inner state. -/
theorem actual_root_direct_certificate (w : α→ℝ)
    (hlo : Cycle153.Root.floor+Cycle153.Root.mesh≤Cycle153RootStep.rootSourceCell w)
    (hhi : Cycle153RootStep.rootSourceCell w≤Cycle153.MarkedRootPrice.top)
    (deltaMax sourcePad omegaMax : ℝ)
    (hsmall : deltaMax+sourcePad+2*omegaMax≤1/1000000000) :
    let r:=Cycle153.MarkedRootPrice.q/(6*slotPrice)
    let b:=Cycle153RootStep.rootSourceCell w
    (r*(Cycle63.AffineLedger.g b+6*Cycle63.AffineLedger.amp b)-
        Cycle63.AffineLedger.amp b)+Cycle63.AffineLedger.lowReserve+
      r*(deltaMax+sourcePad)+2*r*omegaMax≤
      r*(1-6*Cycle63.AffineLedger.amp b-2*Coordinates.mu) := by
  dsimp only
  rw [Cycle153.MarkedRootPrice.affine_amp_eq]
  have hr : 0≤Cycle153.MarkedRootPrice.q/(6*slotPrice) ∧
      Cycle153.MarkedRootPrice.q/(6*slotPrice)≤1 := by
    norm_num [Cycle153.MarkedRootPrice.q,Cycle153.FixedStages.stage0,slotPrice,betaBound]
  have hm:=Cycle153RootStep.root_direct_room (Cycle153RootStep.rootSourceCell w) hlo hhi
  exact direct_certificate_from_room hr.1 hr.2 hm hsmall

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_inner_direct_certificate
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_direct_certificate
