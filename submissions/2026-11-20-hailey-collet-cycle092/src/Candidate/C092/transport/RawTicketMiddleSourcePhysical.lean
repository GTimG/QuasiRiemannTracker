/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
True long reference labels from the physical numerator Y and complete-label
coefficient dilation. The dilation is used for its window, with no extra fee. -/
import Candidate.C092.transport.RawTicketMiddleSourceCore
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open QRH.Cycle090

/-- The P14 numerator exponent is (h-2ell)/D on the literal old band.
Its long reference 1-n0+v+collar stays in BOTH original primal endpoints. -/
theorem physical_reference_in_primal {h D D₀ v vcut collar : ℝ}
    (hh : hLower≤ h ∧ h≤ hUpper) (hD₀ : Dmin≤ D₀)
    (hD : D₀≤ D ∧ D≤ h+rowPad) (hv : 0≤ v ∧ v≤ vcut)
    (hc : 0≤ collar ∧ collar≤ oldAnn) :
    primalLo D₀≤1-(h-2*ell)/D+v+collar ∧
    1-(h-2*ell)/D+v+collar≤ primalHi vcut := by
  have hD₀pos : 0< D₀ := lt_of_lt_of_le (by norm_num [Dmin]) hD₀
  have hDpos : 0< D := hD₀pos.trans_le hD.1
  have hp : 0< rowPad := by unfold rowPad;positivity
  have hh0 : 0< hLower := by norm_num [hLower]
  have hHp : 0< h+rowPad := by linarith only [hh0,hh.1,hp]
  have hLp : 0< hLower+rowPad := by linarith only [hh0,hp]
  have hnumer : 0≤ h-2*ell := by
    have hconst : 0< hLower-2*ell := by norm_num [hLower,ell,theta]
    linarith only [hconst,hh.1]
  have hupper:=div_le_div₀ (by norm_num [hUpper,ell,theta] : 0≤ hUpper-2*ell)
    (show h-2*ell≤ hUpper-2*ell by linarith only [hh.2]) hD₀pos hD.1
  have hDquot:=div_le_div₀ hnumer (le_refl (h-2*ell)) hDpos hD.2
  have hHquot : (hLower-2*ell)/(hLower+rowPad)≤(h-2*ell)/(h+rowPad) := by
    apply (div_le_div_iff₀ hLp hHp).mpr
    have hcoef : 0≤ rowPad+2*ell := by
      have hell : 0< ell := by norm_num [ell,theta]
      linarith only [hp,hell]
    nlinarith only [mul_nonneg (show 0≤ h-hLower by linarith only [hh.1]) hcoef]
  have hnLow : (hLower-2*ell)/(hLower+rowPad)≤(h-2*ell)/D := hHquot.trans hDquot
  have hid : 1-(hLower-2*ell)/(hLower+rowPad)=(2*ell+rowPad)/(hLower+rowPad) := by
    field_simp;ring
  have hbase:= (rounding (x:=(2*ell+rowPad)/(hLower+rowPad)) (n:=10^(15:ℕ)) (by norm_num)).2.2.1
  have htop:= (rounding (x:=ceilAt ((2*ell+rowPad)/(hLower+rowPad)) (10^(15:ℕ))+vcut+oldAnn) (n:=10^(15:ℕ)) (by norm_num)).2.2.1
  constructor
  · dsimp [primalLo]
    linarith only [hupper,hv.1,hc.1]
  · dsimp [primalHi]
    have href : 1-(h-2*ell)/D≤(2*ell+rowPad)/(hLower+rowPad) := by rw [←hid];linarith only [hnLow]
    linarith only [href,hv.2,hc.2,hbase,htop]

/-- A max comparison of old/new labels preserves the same long upper window,
provided BOTH old and new windows retain their literal old raw support bound. -/
theorem compared_reference_upper {old n0 v collar : ℝ}
    (ho : old≤1-n0+v+collar) (h0 : 0≤ v+collar) :
    max old (1-n0)≤1-n0+v+collar := max_le ho (by linarith only [h0])

/-- Literal box upper edge plus the retained Fourier collar. This is the
window used by the moving-scale theorem; it does not spend dilation twice. -/
theorem coefficient_window_collar (n0 v xi ann : ℝ) :
    (1+v+xi+ann-n0)+xi=1-n0+v+(2*xi+ann) := by ring

/-- Small original mesh/collar gates allow the actual reference window to
use the same original annular allowance. -/
theorem coefficient_collar_admitted {xi ann : ℝ}
    (hx : 0≤ xi ∧ xi≤ oldAnn/4) (ha : 0≤ ann ∧ ann≤ oldAnn/2) :
    0≤2*xi+ann ∧ 2*xi+ann≤ oldAnn := by constructor <;> linarith only [hx.1,hx.2,ha.1,ha.2]

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.physical_reference_in_primal
