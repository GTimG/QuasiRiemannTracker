/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P.6 uses a fourth-moment mark quota before Cauchy. Its contribution to the
pair energy is half that quota on both sides of unit radius. -/
import Candidate.C092.Source
set_option autoImplicit false
namespace QRH.Cycle092.NativeFourthEffective
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

def credit (n V : ℝ) : ℝ := if V ≤ 1 then (V/2-n)/2 else V*(1/2-n)/2

def price (n y e ν V deficit : ℝ) : ℝ :=
  ν*y + e*(sourceWidth n y-(u:ℝ)-credit n V) - V*deficit/2

theorem credit_at_one (n : ℝ) : credit n 1 = (1/2-n)/2 := by simp [credit]

/-- Only the certificate at V=1 is needed above one. Both the true mark
credit and the nonnegative count deficit improve as V increases. -/
theorem above_one_paid {n y e ν V deficit : ℝ} (hn : n ≤ 1/2) (he : 0 ≤ e)
    (hV : 1 < V) (hd : 0 ≤ deficit) (hp : price n y e ν 1 deficit < radialAllowance 1) :
    price n y e ν V deficit < radialAllowance V := by
  have hcap : credit n 1 ≤ credit n V := by
    rw [credit_at_one,credit,if_neg (not_le.mpr hV)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hV.le) (sub_nonneg.mpr hn)]
  have hcost : price n y e ν V deficit ≤ price n y e ν 1 deficit := by
    unfold price
    nlinarith only [mul_le_mul_of_nonneg_left hcap he,mul_le_mul_of_nonneg_right hV.le hd]
  have ha : radialAllowance V = radialAllowance 1 := by
    unfold radialAllowance
    rw [max_eq_left (sub_nonpos.mpr (H_real_bounds.2.le.trans hV.le)),
        max_eq_left (sub_nonpos.mpr H_real_bounds.2.le)]
  rw [ha]
  exact hcost.trans_lt hp

theorem corrected_short_price {n y e ν r V : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y) (he : 0 ≤ e) (heν : e ≤ ν) (hν : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hr₀ : 367/500 ≤ r)
    (hr : (c.inverse:ℝ) ≤ r) (hr₁ : r ≤ 1) (hV : (98/100:ℝ) ≤ V) (hp : PaidWithBand y e ν c) :
    price n y e ν V (ν*r+e*inverseQuota r) < radialAllowance V := by
  have hd : 0 ≤ ν*r+e*inverseQuota r := add_nonneg (mul_nonneg (he.trans heν) (by linarith))
    (mul_nonneg he (inverseQuota_nonneg hr₀ hr₁))
  have hb {v : ℝ} (hv : (98/100:ℝ) ≤ v) (hv' : v ≤ 1) :
      price n y e ν v (ν*r+e*inverseQuota r) < radialAllowance v := by
    simpa only [price,credit,actualInversePrice,nativeFourthCap,if_pos hv'] using
      checked_inverse_pays_all_radii (n:=n) c hy hn he heν hν hg hr₀ hr hr₁ hv hp
  by_cases hv : V ≤ 1
  · exact hb hV hv
  · apply above_one_paid _ he (lt_of_not_ge hv) hd (hb (by norm_num) le_rfl)
    have h := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
    norm_num [sourceRatio,sourceY] at h; linarith

theorem corrected_long_price {n y e ν r V : ℝ} (c : Cutoff)
    (hy₀ : (369/1000:ℝ) ≤ y) (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (heν : e ≤ ν) (hν : ν ≤ 3/4) {b : ℚ} (hg : CutoffGuard b c)
    (hr₀ : 1 ≤ r) (hr : r ≤ (c.inverse:ℝ)+(c.ordinary:ℝ)) (hV : (98/100:ℝ) ≤ V)
    (hp : PaidWithBand y e ν c) :
    price n y e ν V (longDeficit ν r) < radialAllowance V := by
  have hd := paid_longDeficit_positive c hy₀ hy he heν hν hg hr hp
  have hb {v : ℝ} (hv : (98/100:ℝ) ≤ v) (hv' : v ≤ 1) :
      price n y e ν v (longDeficit ν r) < radialAllowance v := by
    simpa only [price,credit,actualLongPrice,nativeFourthCap,if_pos hv'] using
      checked_long_pays_all_radii (n:=n) c hy₀ hy hn he heν hν hg hr₀ hr hv hp
  by_cases hv : V ≤ 1
  · exact hb hV hv
  · apply above_one_paid _ he (lt_of_not_ge hv) hd.le (hb (by norm_num) le_rfl)
    have h := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
    norm_num [sourceRatio,sourceY] at h; linarith

#print axioms corrected_short_price
#print axioms corrected_long_price
end
end QRH.Cycle092.NativeFourthEffective
