/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ChosenAnalyticSchedule

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open Cycle153SourceSchedule Cycle153AnalyticPrimitive

/-- The flat profile/height envelope pays the child error with coefficient
one. This is the literal flat OLD source exponent; no multiplication by
its retained width is silently reinstated. The native deletion price and
its actual positive detector surcharge remain unchanged. -/
theorem chosen_native_flat_old_exponent_paid [Cycle63.AffineLedger]
    (cell : ℝ) {eps u coefficientFee nominal width mesh : ℝ}
    (heps : 0<eps) (hfee : coefficientFee≤nativeMu/1024)
    (hunit : u=nominal+width) :
    u+oldLoss eps+Cycle63.AffineLedger.q*
      ((Cycle63.AffineLedger.regionGap cell+
          6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp cell)/
        (6*Cycle63.AffineLedger.price)+detectorExtra)+
      coefficientFee+2*oldLoss eps+Cycle63.AffineLedger.q*mesh≤
      nominal+Cycle63.AffineLedger.amp cell+
        (width-Cycle63.AffineLedger.lowReserve+nativeMu/8+Cycle63.AffineLedger.q*mesh)-
          15*nativeMu/128 := by
  have hchild : oldLoss eps≤ mu/1024 := by
    simpa only [←chosen_native_mu] using (oldLoss_bounds eps).2
  have hterminal : 2*oldLoss eps≤2*mu/1024 := by linarith only [hchild]
  have hfee' : coefficientFee≤ mu/1024 := by simpa only [←chosen_native_mu] using hfee
  have hroom := (old_extra_room Cycle63.AffineLedger.q_pos.le
    Cycle63.AffineLedger.q_le_one (u:=1) le_rfl
    (oldLoss_pos heps).le hchild hfee' hterminal).1
  have hprice := native_affine_deletion_identity cell
  rw [←chosen_native_mu] at hroom
  nlinarith only [hroom,hprice,hunit]

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.chosen_native_flat_old_exponent_paid
