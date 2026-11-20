/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine earlier P.1 quota on actual P14 mixed rows and all original slots.
The analytic premise is ONLY the earlier P.1 pair source. -/
import Candidate.C092.transport.RawTicketMiddleSourcePhysical
import Candidate.C092.transport.MixedPacketWitnessMarks
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.StrongPair
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic ProbeHighRowFamily
open HeckeDetectorRawFiber

/-- No full-slot supply is assumed: it is the literal supply field of the
actual original source fiber. Original slots and widths remain unchanged. -/
theorem actual_slot_quota {M : Ideal ActualEisensteinCubic.O}
    {H : Subgroup (ActualEisensteinCubic.O⧸M)ˣ} {Label Slots : Type}
    {U a epsilon cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slots U a epsilon cutoff T allowance i)
    {n z decrement : ℝ} (hn : nLo≤ n ∧ n≤ nHi) (hz : widthLo≤ z ∧ z≤ widthHi)
    (hd : 0< decrement ∧ decrement≤1/1000) :
    let l:=QRH.Cycle090.sourceWidth n z-decrement
    0≤ l ∧ l< QRH.Cycle090.sourceWidth n z ∧
      l≤∑s∈F.slots,F.widths s := by
  have hq:=true_source_quota hn hz hd
  exact ⟨hq.1,hq.2.1,hq.2.2.trans F.supply⟩

/-- Actual P14 label geometry places the new long reference in the OLD
primal interval. No refined B or middle return power is assumed here. -/
theorem actual_middle_reference {r : Row} (hr : r∈rows) (sep : ℝ)
    {h D v collar : ℝ} (hh : hLower≤ h ∧ h≤ hUpper)
    (hD : Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep≤ D ∧ D≤ h+rowPad)
    (hv : 0≤ v ∧ v≤ funded (oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep)
      (Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep*(r.box.uLo:ℝ)/4))
    (hc : 0≤ collar ∧ collar≤ oldAnn) :
    nLo≤1-(h-2*ell)/D+v+collar ∧ 1-(h-2*ell)/D+v+collar≤ nHi := by
  have hb:=every_original_band hr sep
  have he:=row_endpoint_hull hr
  have hwin:=physical_reference_in_primal hh hb.2.1 hD hv hc
  have hvcut:=(original_thresholds_uniform hb.1 hb.2.1 he.1.1 he.2.1.2 he.2.2.2.2).1
  have hwide:=original_primal_band hb.2.1 hvcut
  exact ⟨hwide.1.trans hwin.1,hwin.2.trans hwide.2⟩

/-- At every actual mixed terminal, the TRUE source width is open and
admitted by P.1 before any actual slot set, ray dictionary, profile or height.
The old conductor band and true dilation box, not the refined B, set nref. -/
theorem actual_middle_source (hP1 : EarlierP1) {r : Row} (hr : r∈rows) (sep : ℝ)
    {h D v collar z decrement : ℝ} (hh : hLower≤ h ∧ h≤ hUpper)
    (hD : Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep≤ D ∧ D≤ h+rowPad)
    (hv : 0≤ v ∧ v≤ funded (oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep)
      (Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep*(r.box.uLo:ℝ)/4))
    (hc : 0≤ collar ∧ collar≤ oldAnn) (hz : widthLo≤ z ∧ z≤ widthHi)
    (hd : 0< decrement ∧ decrement≤1/1000) :
    let nref:=1-(h-2*ell)/D+v+collar
    let l:=QRH.Cycle090.sourceWidth nref z-decrement
    sourceY0≤ z ∧ z≤ sourceY ∧ z≤ nref ∧ nref≤ sourceRatio*z ∧
    0≤ l ∧ l< QRH.Cycle090.sourceWidth nref z ∧ l≤7/37 ∧ PairUniformBox nref z l := by
  have hn:=actual_middle_reference hr sep hh hD hv hc
  have hdomain:=true_source_ordered_domain hn hz
  have hquota:=true_source_quota hn hz hd
  refine ⟨hdomain.1,hdomain.2.1,hdomain.2.2.1,hdomain.2.2.2,hquota.1,hquota.2.1,hquota.2.2,?_⟩
  exact hP1 _ _ hdomain.1 hdomain.2.1 hdomain.2.2.1 hdomain.2.2.2 _ hquota.1 hquota.2.1

/-- The actual coefficient box's mesh/collar produces precisely the long
window required by the source, with both positive quantities retained. -/
theorem actual_coefficient_window {r : Row} (hr : r∈rows) (sep : ℝ)
    {h D v xi ann : ℝ} (hh : hLower≤ h ∧ h≤ hUpper)
    (hD : Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep≤ D ∧ D≤ h+rowPad)
    (hv : 0≤ v ∧ v≤ funded (oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep)
      (Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep*(r.box.uLo:ℝ)/4))
    (hxi : 0≤ xi ∧ xi≤ oldAnn/4) (hann : 0≤ ann ∧ ann≤ oldAnn/2) :
    let m:=1+v+xi+ann-(h-2*ell)/D
    let nref:=1-(h-2*ell)/D+v+(2*xi+ann)
    nLo≤ nref ∧ nref≤ nHi ∧ m+xi=nref := by
  have hn:=actual_middle_reference hr sep hh hD hv (coefficient_collar_admitted hxi hann)
  exact ⟨hn.1,hn.2,coefficient_window_collar _ _ _ _⟩

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.actual_slot_quota
#print axioms QRH.Cycle092.RawTicket.actual_middle_source
#print axioms QRH.Cycle092.RawTicket.actual_coefficient_window
