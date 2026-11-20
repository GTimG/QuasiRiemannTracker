/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained small-box references and the single true dilation window. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceCount
import Candidate.C092.transport.MixedPacketScaleWindow
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor Cycle25.Weighted.Numerator
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.RawTicket QRH.Cycle092.MixedTicketTails
local notation "O" => HeckeFamily.O

def paidReference (n0 v xi ann : ℝ) : ℝ := 1-n0+v+(2*xi+ann)
def paidWindow (n0 v xi ann : ℝ) : ℝ := 1+v+xi+ann-n0

theorem paid_reference (h : ℝ) (hh : hLower ≤ h ∧ h ≤ hUpper)
    {r : Row} (hr : r∈rows) {d v xi ann : ℝ}
    (hd : originalDlow r ≤ d ∧ d ≤ h+rowPad)
    (hv : 0 ≤ v ∧ v ≤ originalVcut r) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcollar : 2*xi+ann ≤ witnessCollar) :
    let n0 := (h-2*ell)/d
    nLo ≤ paidReference n0 v xi ann ∧ paidReference n0 v xi ann ≤ nHi ∧
    0 ≤ paidWindow n0 v xi ann ∧
    paidWindow n0 v xi ann+xi=paidReference n0 v xi ann ∧
    paidReference n0 v xi ann ≤ 1-n0+v+witnessCollar := by
  have hxiOld : xi ≤ oldAnn/4 := by norm_num [oldAnn,witnessCollar] at hcollar ⊢;linarith
  have hannOld : ann ≤ oldAnn/2 := by norm_num [oldAnn,witnessCollar] at hcollar ⊢;linarith
  have hn := actual_coefficient_window hr (originalSep r) hh hd hv ⟨hxi,hxiOld⟩ ⟨hann,hannOld⟩
  dsimp only
  have hsum : paidWindow ((h-2*ell)/d) v xi ann+xi=paidReference ((h-2*ell)/d) v xi ann := by
    dsimp [paidWindow,paidReference];ring
  refine ⟨hn.1,hn.2.1,?_,hsum,?_⟩
  · have hx : xi ≤ witnessCollar/2 := by linarith
    have hlo := hn.1
    change nLo ≤ paidReference ((h-2*ell)/d) v xi ann at hlo
    norm_num [nLo,witnessCollar] at hx hlo ⊢
    linarith
  · dsimp [paidReference];linarith

/-- Literal numerator Y at the true conductor scale U=Z^d. -/
theorem paid_numerator_scale {Z d y : ℝ} (hZ : 0<Z) (hd : d≠0) :
    Z^y=(Z^d)^(y/d) := by
  rw [←Real.rpow_mul hZ.le,mul_div_cancel₀ _ hd]

/-- The same actual max-one tuple dilation supplies the retained long window.
The annular allowance enlarges that window only; it is not a second dilation fee. -/
theorem paid_tuple_window (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (u : FreeRow) (data : PhysicalReflectionData S hS u)
    {U N Y n0 v xi ann : ℝ} (hU : 1<U) (hN : 0<N) (hY : Y=U^n0)
    (hrow : rowNorm u ≤ U) (hann : 0 ≤ ann)
    (hedge : max 1 (data.combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u)*N)
      ≤ U^(v+xi)) :
    data.combinedConductor ≤ (fixedConductorConstant S:ℝ)*
      U^(paidWindow n0 v xi ann)*(Y/N) := by
  have hh := MixedPacketScale.true_dilation_window S hS u data U N Y n0 (v+xi)
    (zero_lt_one.trans hU) hN hrow hY hedge
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (by rw [hY];positivity) hN.le)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hU.le
  dsimp [paidWindow];linarith

#print axioms paid_reference
#print axioms paid_tuple_window
end
end QRH.Cycle092.MixedMiddleReturn
