/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original complete-label dilation supplies the actual Fourier window of
P.1; this reuses the proved physical dilation theorem, without a second debit. -/
import Candidate.C092.transport.RawTicketMiddleSourceActual
import Candidate.C092.transport.MixedPacketScaleWindow
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.StrongPair
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical ProbeRowRadicalConductor Cycle25.Weighted.Numerator
local notation "O" => HeckeFamily.O

/-- Positive actual Fourier window, with the collar accounted for once. -/
theorem middle_window_nonneg {nref m xi : ℝ} (hn : nLo≤ nref)
    (hx : xi≤ oldAnn/4) (heq : m+xi=nref) : 0≤ m ∧ 0≤ nref := by
  norm_num [nLo,oldAnn] at hn hx
  constructor <;> linarith only [hn,hx,heq]

/-- One genuine physical complete coefficient tuple is admitted by earlier P.1
at the actual long reference. Quantification over u, data and N permits every
independent tuple choice; the original ordinary and mark dictionaries are
those quantified by PairUniformBox, with its mesh before actual slots. -/
theorem actual_middle_tuple_source (hP1 : EarlierP1)
    {r : Row} (hr : r∈rows) (sep : ℝ)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (data : PhysicalReflectionData S hS u)
    {h D v xi ann z decrement U N Y : ℝ}
    (hh : hLower≤ h ∧ h≤ hUpper)
    (hD : Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep≤ D ∧ D≤ h+rowPad)
    (hv : 0≤ v ∧ v≤ funded (oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep)
      (Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep*(r.box.uLo:ℝ)/4))
    (hxi : 0≤ xi ∧ xi≤ oldAnn/4) (hann : 0≤ ann ∧ ann≤ oldAnn/2)
    (hz : widthLo≤ z ∧ z≤ widthHi) (hdec : 0< decrement ∧ decrement≤1/1000)
    (hU : 0< U) (hN : 0< N) (hrow : rowNorm u≤ U) (hY : Y=U^((h-2*ell)/D))
    (hbox : max 1 (data.combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u)*N)
      ≤ U^(v+xi+ann)) :
    let m:=1+v+xi+ann-(h-2*ell)/D
    let nref:=1-(h-2*ell)/D+v+(2*xi+ann)
    let l:=QRH.Cycle090.sourceWidth nref z-decrement
    0≤ m ∧ m+xi=nref ∧
    data.combinedConductor≤(fixedConductorConstant S:ℝ)*U^m*(Y/N) ∧
    0≤ l ∧ l< QRH.Cycle090.sourceWidth nref z ∧ l≤7/37 ∧ PairUniformBox nref z l := by
  have hgeom:=actual_coefficient_window hr sep hh hD hv hxi hann
  have hsource:=actual_middle_source hP1 hr sep hh hD hv
    (coefficient_collar_admitted hxi hann) hz hdec
  have hwin:=QRH.Cycle092.MixedPacketScale.true_dilation_window S hS u data U N Y
    ((h-2*ell)/D) (v+xi+ann) hU hN hrow hY hbox
  have heq : 1+(v+xi+ann)-(h-2*ell)/D=1+v+xi+ann-(h-2*ell)/D := by ring
  rw [heq] at hwin
  refine ⟨(middle_window_nonneg hgeom.1 hxi.2 hgeom.2.2).1,hgeom.2.2,hwin,
    hsource.2.2.2.2.1,hsource.2.2.2.2.2.1,hsource.2.2.2.2.2.2.1,hsource.2.2.2.2.2.2.2⟩

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.actual_middle_tuple_source
