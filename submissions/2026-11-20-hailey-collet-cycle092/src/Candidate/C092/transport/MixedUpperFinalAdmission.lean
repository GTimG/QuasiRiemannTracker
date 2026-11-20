/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual mixed row admission supplies the true full Q.2 cutoff bank. -/
import Candidate.C092.transport.MixedUpperFinalPartition
import Candidate.C092.transport.MixedOutsidePaidPrice
import Candidate.C092.transport.MixedCenteredCertificate
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.RawTicket
open QRH.Cycle092.MixedTicketTails QRH.Cycle092.MixedOutsidePaid
open QRH.Cycle092.PacketJoinE49 QRH.Cycle092.PacketJoinE49.Return
variable [QRH.Record1252270103Return.Geometry.Parameters]

/-- The original actual row, rather than a chosen abstract bank, fixes
admissible endpoints and the predecessor amplification factor. -/
theorem original_bank_admission {r : Row} (hr : r∈rows) {δ p : ℝ}
    (hp : r.box.Contains (δ,p)) :
    Return.window.Available δ p ∧
    0 ≤ (rowGamma r.box r.B:ℝ) ∧ (rowGamma r.box r.B:ℝ) ≤ gammaMax ∧
    1 ≤ Return.cutoffI δ p-(rowGamma r.box r.B:ℝ) ∧ Return.cutoffI δ p ≤ 3/2 ∧
    δ*((rowV r.box:ℝ)/(r.box.uHi:ℝ)) ≤ 5/6-δ := by
  have hav:=original_e49_available hr hp
  have hc:=actual_crossing_bounds hr hp actual_contact_root
  rw [←actual_contact_width,←actual_contact_intercept,←actual_contact_slope,
    ←actual_cutoff_eq δ p (Return.hJ hav.1 hav.2).ne'] at hc
  have hgn:0 ≤ (rowGamma r.box r.B:ℝ):=(row_inner_parameters hr).2.2.2.2.2.1
  have hg:=(every_inner_gamma_bound hr)
  have hgl : innerGammaMax ≤ gammaMax:=by norm_num [innerGammaMax,gammaMax]
  have hlow : 1<tLo-innerGammaMax:=by norm_num [tLo,innerGammaMax]
  have hhi : tHi<3/2:=by norm_num [tHi]
  refine ⟨hav,hgn,hg.trans hgl,by linarith only [hc.1,hg,hlow],by linarith only [hc.2,hhi],?_⟩
  exact (QRH.Cycle092.MixedCenteredFaces.directed_parameters hr hp).2.2

#print axioms original_bank_admission
end
end QRH.Cycle092.MixedUpperFinal
