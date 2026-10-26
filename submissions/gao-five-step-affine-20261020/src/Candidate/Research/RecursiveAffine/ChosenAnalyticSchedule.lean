/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextHighPrimitive
import Candidate.Research.RecursiveAffine.AnalyticPrimitive
import Candidate.Research.RecursiveAffine.IndependentNodeError

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open scoped Classical HeckeNotation ContDiff
open Set HeckeFamily Cycle63InitialMass Cycle153RegionalState

/-- The active source constants are exactly the audited constants. -/
theorem chosen_analytic_error : Cycle153.RegionalSchedule.primitiveError=
    Cycle153AnalyticPrimitive.analyticError := rfl
theorem chosen_native_mu : nativeMu=Cycle153AnalyticPrimitive.mu := rfl
theorem chosen_old_error (eps : ℝ) : oldLoss eps=Cycle153AnalyticPrimitive.nodeError eps := rfl
theorem chosen_driver_rate (N : ℕ) : nativeDriverRate N=Cycle153AnalyticPrimitive.driverRate N := rfl

/-- This is the actual selected OLD exponent with the chosen child and
terminal errors. Its deletion price is proved from the native ledger;
the actual detector surcharge is paid inside the existing native fee. -/
theorem chosen_native_old_exponent_paid [Cycle63.AffineLedger]
    (cell : ℝ) {eps u coefficientFee nominal width mesh : ℝ}
    (heps : 0<eps) (hu1 : u≤1) (hfee : coefficientFee≤nativeMu/1024)
    (hunit : u=nominal+width) :
    u*(1+oldLoss eps)+Cycle63.AffineLedger.q*
      ((Cycle63.AffineLedger.regionGap cell+
          6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp cell)/
        (6*Cycle63.AffineLedger.price)+Cycle153AnalyticPrimitive.detectorExtra)+
      coefficientFee+2*oldLoss eps+Cycle63.AffineLedger.q*mesh≤
      nominal+Cycle63.AffineLedger.amp cell+
        (width-Cycle63.AffineLedger.lowReserve+nativeMu/8+Cycle63.AffineLedger.q*mesh)-
          15*nativeMu/128 := by
  have hchild : oldLoss eps≤Cycle153AnalyticPrimitive.mu/1024 := by
    simpa only [←chosen_native_mu] using (oldLoss_bounds eps).2
  have hterminal : 2*oldLoss eps≤2*Cycle153AnalyticPrimitive.mu/1024 := by
    linarith only [hchild]
  have h:=Cycle153AnalyticPrimitive.native_selected_old_exponent_paid cell (mesh:=mesh) hu1
    (oldLoss_pos heps).le hchild (by simpa only [←chosen_native_mu] using hfee) hterminal hunit
  simpa only [←chosen_native_mu] using h

/-- The actual AtState source theorem constructs this small OLD exponent
while retaining the chosen larger analytic source loss. -/
theorem chosen_small_error_at_state
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc 1 2)
    (hbetaLo : 51/100≤HeckeZeroSupremum.beta) (hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (bPhi Bmask mesh eps : ℝ) :
    RegionalAtStateStatement (α:=alpha) M H hH W hW hWs hbetaLo hbetaHi
      g Cycle153.RegionalSchedule.primitiveError bPhi Bmask mesh (oldLoss eps) := by
  exact Cycle153AnalyticPrimitive.actual_small_error_at_state M H hH
    W hW hWs hbetaLo hbetaHi g bPhi Bmask mesh eps

end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.chosen_native_old_exponent_paid
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.chosen_small_error_at_state
