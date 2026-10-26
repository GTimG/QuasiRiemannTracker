/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Generalization of Record12518109Gain.FiberExponent to an earlier ordinary face.
The four premises are separate primitive moment/count gates for the same row
fiber. The marked ordinary gate retains both cap and affine restrictions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.Thresholds

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section

theorem fiber_exponent {nu B lam h x t p S r m E loss eps zeta : ℝ}
    (hnu0 : 1/2≤nu) (hnu1 : nu≤3/4) (hlam : 1<lam) (hh : 0≤h)
    (hx0 : 5/6≤x) (hxB : x≤B) (hB : B≤1)
    (hbalance : 6*nu*x+(5-6*nu)*t=5)
    (hcut : t=inverseThreshold x S 1+plainThreshold B lam h x S 1/2)
    (hp0 : 0≤p) (hp : p≤1/2) (hS : 0≤S)
    (heps : 0≤eps) (heps1 : eps≤1/100) (hzeta : 0<zeta)
    (hlen : t-eps≤r+m) (hr : r≤t+eps)
    (hI : E≤max 1 ((1+5*r)/6)-nu*r+loss)
    (hP : E≤1-2*nu*m+loss)
    (hIM : ∀z : ℝ,0≤z → z≤S → r+2*z<1 → 2*r+8*z<3 →
      E≤1-nu*r-2*nu*p*z+loss)
    (hPM : ∀z : ℝ,0≤z → z≤S → z≤h → 2*m+lam*z≤B →
      E≤1-2*nu*m-2*nu*p*z+loss) :
    E+2*nu*p*S≤1-nu*x+nu*S+loss+eps+nu*zeta := by
  have hv : 0<nu := by linarith
  have hx : x≤1 := hxB.trans hB
  have hl : 0<lam := by linarith
  have hcredit0 : 0≤nu*(1-2*p)*S :=
    mul_nonneg (mul_nonneg hv.le (by linarith)) hS
  suffices hh : E-nu*(1-2*p)*S≤1-nu*x+loss+eps+nu*zeta by nlinarith
  by_cases hr1 : r≤1
  · rw [max_eq_left (by linarith : (1+5*r)/6≤1)] at hI
    by_cases hmB : 2*m≤B
    · rcases same_zero_alternative (B:=B) (lam:=lam) (h:=h) (x:=x) (S:=S) (Q:=1)
        (r:=r) (m:=m) (eps:=eps) (by rw [←hcut]; exact hlen) with hrt|hmt
      · let z0 := min S ((1-r)/2)
        let z := max 0 (z0-zeta)
        have hz00 : 0≤z0 := le_min hS (by linarith)
        have hz0S : z0≤S := min_le_left _ _
        have hz0cap : z0≤(1-r)/2 := min_le_right _ _
        have hz : 0≤z := le_max_left _ _
        have hzz0 : z≤z0 := max_le hz00 (by linarith)
        have hzS : z≤S := hzz0.trans hz0S
        have hzloss : z0-zeta≤z := le_max_right _ _
        have ht0 : x-S≤ inverseThreshold x S 1 := le_max_left _ _
        have ht1 : 2*x-1≤ inverseThreshold x S 1 := le_max_right _ _
        have htarget : x-eps-zeta≤r+z := by
          have hmin : x-eps≤r+z0 := by
            dsimp [z0]
            rw [add_min]
            exact le_min (by linarith) (by linarith)
          linarith
        have hcredit := amplitude_credit hv.le hp hzS
        by_cases hzz : z=0
        · rw [hzz] at htarget
          have ht := mul_le_mul_of_nonneg_left htarget hv.le
          nlinarith
        · have hze : z=z0-zeta := by
            by_cases hz0 : 0≤z0-zeta
            · exact max_eq_right hz0
            · exact False.elim (hzz (max_eq_left (le_of_not_ge hz0)))
          have hcap1 : r+2*z<1 := by rw [hze]; linarith
          have hcap2 : 2*r+8*z<3 := by linarith
          have hc := hIM z hz hzS hcap1 hcap2
          have ht := mul_le_mul_of_nonneg_left htarget hv.le
          nlinarith
      · let z := min S (min h ((B-2*m)/lam))
        have hz : 0≤z := le_min hS (le_min hh (div_nonneg (by linarith) hl.le))
        have hzS : z≤S := min_le_left _ _
        have hzh : z≤h := (min_le_right _ _).trans (min_le_left _ _)
        have hzcap : 2*m+lam*z≤B := by
          have hc : z≤(B-2*m)/lam := (min_le_right _ _).trans (min_le_right _ _)
          have hc' := (le_div_iff₀ hl).mp hc
          nlinarith
        have htarget : x≤2*m+z := by
          simpa only [mul_one] using (plain_threshold_iff hlam).mp hmt
        have hcredit := amplitude_credit hv.le hp hzS
        have hc := hPM z hz hzS hzh hzcap
        have ht := mul_le_mul_of_nonneg_left htarget hv.le
        have hzz : 0≤nu*zeta := by positivity
        nlinarith
    · have ht : nu*x≤2*nu*m := by nlinarith
      have hzz : 0≤nu*zeta := by positivity
      linarith
  · rw [max_eq_right (by linarith : 1≤(1+5*r)/6)] at hI
    have ht := mul_le_mul_of_nonneg_left hr (show 0≤5/6-nu by linarith)
    have hzz : 0≤nu*zeta := by positivity
    nlinarith

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.fiber_exponent
