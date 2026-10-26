/- Actual bare-root native direct/reflection envelope. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSourceGates
import Candidate.Research.RecursiveAffine.NativeDirectCertificate
import Candidate.Research.RecursiveAffine.ActualRootNativeFee
import Candidate.Research.RecursiveAffine.ActualRootSourceThresholds

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Cycle153.RegionalSchedule CenteredMomentCommonRadialData
open Filter HeckeFamily CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization Cycle63InitialMass Cycle153RootStep Cycle153SourceSchedule
open Cycle63.Optimization
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
noncomputable local instance rootCanonicalEnvelopeLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

/-- The genuine root cell and chosen native small-loss schedule imply
its direct/reflection envelope uniformly before the moving source. No
source envelope, fee, child, energy or returned-count bound is an input. -/
theorem eventually_actual_root_canonical_envelope (budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(s : Input alpha),C.globalBase=Z→
      s.b₁=(9/4:ℝ)→s.b₂=(9/4:ℝ)→Fintype.card alpha ≤ budget→
      (Cycle63.AffineLedger.slotFloor ≤ ∑i,C.originalWeight i ∧
        (∑i,C.originalWeight i) ≤ Cycle63.AffineLedger.slotTop)→
    let omega:=frequencyLoss C.globalBase 32 (nativeMu/64)+nativeMu/8
    let deltaMax:=nativeMu/8+(nativeMu/64)/2
    let omegaMax:=nativeMu/4
    let r:=Cycle63.AffineLedger.q/(6*slotPrice)
    let b:=rootSourceCell C.originalWeight
    0 ≤ omega ∧ omega ≤ omegaMax ∧
      r ≤ 1/2 ∧
      (r*(Cycle63.AffineLedger.g b+6*Cycle63.AffineLedger.amp b)-Cycle63.AffineLedger.amp b)+
        Cycle63.AffineLedger.lowReserve+r*(deltaMax+actualRootSourcePad C s)+2*r*omegaMax ≤
          r*(1-6*Cycle63.AffineLedger.amp b-2*(397/1000:ℝ)) :=by
  obtain ⟨Z0,hZ0,hfreq⟩:=CenteredMomentFirstPhysicalLedger.frequency_loss_eventually 32 (nativeMu/64)
    (by norm_num) (div_pos nativeMu_pos (by norm_num))
  filter_upwards [eventually_ge_atTop Z0,eventually_actual_native_pad budget] with Z hz hp
  refine ⟨hp.1,?_⟩
  intro C s hbase hb1 hb2 hcard hslots omega deltaMax omegaMax r b
  have hf:=hfreq Z hz
  rw [←hbase] at hf
  have hf0:=frequencyLoss_nonneg C.globalBase 32 (nativeMu/64) C.globalBase_gt_one
    (by norm_num) (div_pos nativeMu_pos (by norm_num)).le
  have hpadFull:=hp.2 1 (by norm_num) (Fintype.card alpha) hcard (9/4) s.b₁ s.b₂
    (by norm_num) le_rfl hb1.le hb2.le
  rw [Real.rpow_one,←hbase] at hpadFull
  have hg : 0 ≤ 252/(Cycle153.RegionalSchedule.gridSize:ℝ):=by positivity
  have hlog : 0 ≤ Real.logb C.globalBase 128:=Real.logb_nonneg C.globalBase_gt_one (by norm_num)
  have hpad : actualRootSourcePad C s ≤ 1/(10:ℝ)^20:=by
    dsimp only[actualRootSourcePad]
    linarith only[hpadFull,hg,hlog]
  have hsmall : deltaMax+actualRootSourcePad C s+2*omegaMax ≤ 1/1000000000:=by
    dsimp only[deltaMax,omegaMax]
    norm_num [nativeMu,primitiveError] at *
    linarith only[hpad]
  have hbounds:=Cycle63.AffineLedger.cellUpper_bounds
    (Cycle63.AffineLedger.originalCell_mem hslots).1 (Cycle63.AffineLedger.originalCell_mem hslots).2.1
  have hlo : Cycle153.Root.floor+Cycle153.Root.mesh ≤ b:=hbounds.1
  have hhi : b ≤ Cycle153.MarkedRootPrice.top:=hbounds.2
  have hcert:=actual_root_direct_certificate C.originalWeight hlo hhi deltaMax (actualRootSourcePad C s) omegaMax hsmall
  refine ⟨?_,?_,?_,?_⟩
  · dsimp only[omega];linarith only[hf0,nativeMu_pos]
  · dsimp only[omega,omegaMax];linarith only[hf.2,nativeMu_pos]
  · change Cycle153.MarkedRootPrice.q/(6*slotPrice) ≤ 1/2
    norm_num [Cycle153.MarkedRootPrice.q,Cycle153.FixedStages.stage0,slotPrice,betaBound]
  · dsimp only[r,b]
    change Cycle153.MarkedRootPrice.q/(6*slotPrice)*_ - _ + _ +
      Cycle153.MarkedRootPrice.q/(6*slotPrice)*_ + 2*(Cycle153.MarkedRootPrice.q/(6*slotPrice))*_ ≤
      (Cycle153.MarkedRootPrice.q/(6*slotPrice))*(1-6*Cycle63.AffineLedger.amp (rootSourceCell C.originalWeight)-2*(397/1000:ℝ))
    simpa only[Cycle153Geometry.Coordinates.mu] using hcert
/-- The literal one-femto envelope used by the canonical caller. Its
three coarse error ceilings are fixed constants of the chosen schedule;
the actual source still keeps its measured pad in the returned edge. -/
theorem actual_root_canonical_fixed_envelope (w : alpha→ℝ)
    (hslots : Cycle63.AffineLedger.slotFloor ≤ ∑i,w i ∧
      (∑i,w i) ≤ Cycle63.AffineLedger.slotTop) :
    let r:=Cycle63.AffineLedger.q/(6*slotPrice)
    let b:=rootSourceCell w
    r ≤ 1/2 ∧
    (r*(Cycle63.AffineLedger.g b+6*Cycle63.AffineLedger.amp b)-Cycle63.AffineLedger.amp b)+
      Cycle63.AffineLedger.lowReserve+r*((1/1000000000000000:ℝ)+nativeMu/8)+
        2*r*(1/1000000000000000:ℝ) ≤
          r*(1-6*Cycle63.AffineLedger.amp b-2*(397/1000:ℝ)) :=by
  intro r b
  have hbounds:=Cycle63.AffineLedger.cellUpper_bounds
    (Cycle63.AffineLedger.originalCell_mem hslots).1 (Cycle63.AffineLedger.originalCell_mem hslots).2.1
  have hcert:=actual_root_direct_certificate w hbounds.1 hbounds.2
    (1/1000000000000000) (nativeMu/8) (1/1000000000000000)
    (by norm_num [nativeMu,primitiveError])
  refine ⟨?_,?_⟩
  · change Cycle153.MarkedRootPrice.q/(6*slotPrice) ≤ 1/2
    norm_num [Cycle153.MarkedRootPrice.q,Cycle153.FixedStages.stage0,slotPrice,betaBound]
  · dsimp only[r,b]
    change Cycle153.MarkedRootPrice.q/(6*slotPrice)*_ - _ + _ +
      Cycle153.MarkedRootPrice.q/(6*slotPrice)*_ + 2*(Cycle153.MarkedRootPrice.q/(6*slotPrice))*_ ≤
      (Cycle153.MarkedRootPrice.q/(6*slotPrice))*(1-6*Cycle63.AffineLedger.amp (rootSourceCell w)-2*(397/1000:ℝ))
    simpa only[Cycle153Geometry.Coordinates.mu] using hcert

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.eventually_actual_root_canonical_envelope
