/- Actual direct/wide OLD source exponents at the chosen native detector target.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeFlatOldPayment
import Candidate.Cycle63.Physical.InitialMass.LowChildReturned

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open Cycle153SourceSchedule Cycle63InitialMass Cycle153AnalyticPrimitive
open Cycle153.RegionalSchedule

/-- The actual wide source has the flat child error with coefficient one.
Both source branches fit the SAME native common allowance. The common
term retains the genuine direct radial-padding cost and slot deletion
loss, rather than trying to absorb them into a generic small error. -/
theorem actual_dispatched_old_exponents_paid [Cycle63.AffineLedger]
    (cell : ℝ) {eps u nominal width mesh slotLoss radialPad allowance
      epsOld epsReflect epsChild : ℝ}
    (heps : 0<eps)(hunit : u=nominal+width)
    (hOld : epsOld≤oldLoss eps)(hReflect : epsReflect≤oldLoss eps)
    (hChild : epsChild≤oldLoss eps)(hRadial : 0≤radialPad)(hAllowance : 0≤allowance) :
    let del := (Cycle63.AffineLedger.regionGap cell+
      6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp cell)/
        (6*Cycle63.AffineLedger.price)+detectorExtra
    let common := width-Cycle63.AffineLedger.lowReserve+nativeMu/64+
      slotLoss+radialPad+Cycle63.AffineLedger.q*mesh
    max (u+epsOld+epsReflect+epsChild+slotLoss+Cycle63.AffineLedger.q*(del+mesh))
      (nominal+width+Cycle63.AffineLedger.amp cell-Cycle63.AffineLedger.lowReserve+
        allowance+epsOld+slotLoss+radialPad+Cycle63.AffineLedger.q*mesh)≤
      nominal+Cycle63.AffineLedger.amp cell+common+allowance := by
  intro del common
  have hmu : 0≤nativeMu := by norm_num [nativeMu,primitiveError]
  have hOldSmall : epsOld≤nativeMu/1024 := hOld.trans (oldLoss_bounds eps).2
  have hwide:=chosen_native_flat_old_exponent_paid cell (coefficientFee:=0) (mesh:=mesh)
    heps (by exact div_nonneg hmu (by norm_num)) hunit
  apply max_le
  · dsimp only [del,common] at *
    nlinarith only [hwide,hOld,hReflect,hChild,hRadial,hAllowance,hmu]
  · dsimp only [common]
    linarith only [hOldSmall,hmu]

/-- Scalar transport is proved before substituting dependent physical
geometry projections. It keeps the source-selected geometry unchanged. -/
theorem actual_dispatched_old_exponents_paid_at [Cycle63.AffineLedger]
    (cell : ℝ) {eps u nominal width mesh slotLoss radialPad allowance
      epsOld epsReflect epsChild q amp del : ℝ}
    (heps : 0<eps)(hunit : u=nominal+width)
    (hOld : epsOld≤oldLoss eps)(hReflect : epsReflect≤oldLoss eps)
    (hChild : epsChild≤oldLoss eps)(hRadial : 0≤radialPad)(hAllowance : 0≤allowance)
    (hq : q=Cycle63.AffineLedger.q)(hamp : amp=Cycle63.AffineLedger.amp cell)
    (hdel : del=(Cycle63.AffineLedger.regionGap cell+
      6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp cell)/
        (6*Cycle63.AffineLedger.price)+detectorExtra) :
    max (u+epsOld+epsReflect+epsChild+slotLoss+q*(del+mesh))
      (nominal+width+amp-Cycle63.AffineLedger.lowReserve+
        allowance+epsOld+slotLoss+radialPad+q*mesh)≤
      nominal+amp+(width-Cycle63.AffineLedger.lowReserve+nativeMu/64+
        slotLoss+radialPad+q*mesh)+allowance := by
  subst q;subst amp;subst del
  exact actual_dispatched_old_exponents_paid cell (mesh:=mesh) (slotLoss:=slotLoss)
    heps hunit hOld hReflect hChild hRadial hAllowance

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_dispatched_old_exponents_paid

#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_dispatched_old_exponents_paid_at
