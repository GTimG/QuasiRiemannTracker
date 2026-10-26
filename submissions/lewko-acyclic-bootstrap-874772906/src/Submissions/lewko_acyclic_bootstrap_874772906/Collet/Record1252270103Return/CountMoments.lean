/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.CountSource
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.CountCurve
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Return
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths QRH.Record12518109Count
open HeckeFamily HeckeDetectorRawFiber
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
 {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The clipped and affine portions use the same supported witness and source.
The natural sub-width fallback remains in `moments`, with its original full rows. -/
theorem piecewise_marked_count
 (F : Fiber M H Label Slot U a ε tstar T allowance i)
 {B lam cap sourceCap κplain c κinverse C height εm ν : ℝ}
 (moments : Cycle25DetectorRawFiber.Moments F κplain c κinverse C height εm)
 (affine : AffineMarkedMoment F (broadFace B lam sourceCap) C height εm)
 (hU : 1<U) (ha : 1/2<a) (hk : 0≤κplain) (hC : 0≤C) (hh : 0≤height)
 (hf : 2*Real.pi*allowance+(3*i:ℕ)*T≤height)
 (hm : F.m<1/2) (hm0 : 0≤F.m)
 (hl : 0<lam) (hν : 0≤ν)
 (hz : ν<min cap ((B-2*F.m)/lam))
 (hcap : cap≤sourceCap) (hcapSmall : cap≤7/37) :
 (F.rows.card:ℝ)≤192*(1+height)*C*
  U^(plainCurve B lam cap (2*a-1) (F.q/(2*a-1)) F.m+
    2*F.q*ν+4*ε+(2*a-1)*F.mesh+εm) := by
 let z := min cap ((B-2*F.m)/lam)-ν
 have hδ : 0<2*a-1 := by linarith
 have hq := (F.mean_bounds ha.le).1
 have hp : 0≤F.q/(2*a-1) := div_nonneg hq hδ.le
 have he : (2*a-1)*(F.q/(2*a-1))=F.q := mul_div_cancel₀ _ hδ.ne'
 have hz0 : 0<z := sub_pos.mpr hz
 have hzcap : z≤cap := by dsimp [z];linarith [min_le_left cap ((B-2*F.m)/lam)]
 have hzbudget : lam*z≤B-2*F.m := by
  have hz' : z≤(B-2*F.m)/lam := by dsimp [z];linarith [min_le_right cap ((B-2*F.m)/lam)]
  simpa only [mul_comm] using (le_div_iff₀ hl).mp hz'
 have hb := affine_marked_count F (broadFace B lam sourceCap) moments affine hU ha.le hk hC hh hf hm
  (by exact hm0) (by exact hm.le) (by dsimp [broadFace];linarith) hl hz0
  (hzcap.trans hcapSmall) (hzcap.trans hcap) hzbudget
 have heq : plainCurve B lam cap (2*a-1) (F.q/(2*a-1)) F.m+2*F.q*ν =
  1-2*(2*a-1)*F.m-2*F.q*z := by
  rw [plainCurve_eq B lam cap (2*a-1) (F.q/(2*a-1)) F.m hδ.le hp]
  dsimp [z]
  rw [show 2*(2*a-1)*(F.q/(2*a-1))=2*F.q by nlinarith [he]]
  ring
 rw [heq]
 exact hb
end
end QRH.Record1252270103Return
#print axioms QRH.Record1252270103Return.piecewise_marked_count
