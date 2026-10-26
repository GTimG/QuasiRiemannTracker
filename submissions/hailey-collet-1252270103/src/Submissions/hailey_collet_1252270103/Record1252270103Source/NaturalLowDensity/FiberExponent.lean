/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/FiberExponent.lean. Original formulas and source attribution retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.NaturalLowDensity.Selection

set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.NaturalLowDensity
open Record12518109Gain
noncomputable section

theorem amplitude_credit {ν p S z : ℝ} (hν : 0 ≤ ν) (hp : p ≤ 1/2)
    (hz : z ≤ S) : ν*z ≤ 2*ν*p*z+ν*(1-2*p)*S := by
  nlinarith [mul_nonneg (mul_nonneg hν (show 0 ≤ 1-2*p by linarith)) (sub_nonneg.mpr hz)]

/-- The actual four moment gates imply the homogeneous count. Erosion is
explicit so that no marked moment is used on its forbidden boundary. -/
theorem fiber_exponent {ν p S r m E loss eps ζ : ℝ}
    (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hS : 0 ≤ S) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/100) (hζ : 0 < ζ)
    (hlen : cutoff ν S-eps ≤ r+m) (hr : r ≤ cutoff ν S+eps)
    (hI : E ≤ max 1 ((1+5*r)/6)-ν*r+loss)
    (hP : E ≤ 1-2*ν*m+loss)
    (hIM : ∀ z : ℝ, 0 ≤ z → z ≤ S → r+2*z < 1 → 2*r+8*z < 3 →
      E ≤ 1-ν*r-2*ν*p*z+loss)
    (hPM : ∀ z : ℝ, 0 ≤ z → z ≤ S → 2*m+(9/2)*z ≤ 1 →
      E ≤ 1-2*ν*m-2*ν*p*z+loss) :
    E+2*ν*p*S ≤ rho ν+ν*S-gain ν S 1+loss+eps+ν*ζ := by
  have hv : 0 < ν := by linarith
  obtain ⟨_,hx,hcut0,hcut1,hthreshold⟩ := selection_bounds hν0 hν1 hS
  have hbalance := cutoff_balance hν0 hν1 hS
  have hgain := xi_gain_identity (S:=S) hν0 hν1
  have hcredit0 : 0 ≤ ν*(1-2*p)*S := mul_nonneg (mul_nonneg hv.le (by linarith)) hS
  suffices hh : E-ν*(1-2*p)*S ≤ 1-ν*xi ν S+loss+eps+ν*ζ by nlinarith
  by_cases hr1 : r ≤ 1
  · rw [max_eq_left (by linarith : (1+5*r)/6 ≤ 1)] at hI
    by_cases hm1 : m ≤ 1/2
    · by_cases hrt : inverseThreshold ν S-eps ≤ r
      · let z0 := min S ((1-r)/2)
        let z := max 0 (z0-ζ)
        have hz00 : 0 ≤ z0 := le_min hS (by linarith)
        have hz0S : z0 ≤ S := min_le_left _ _
        have hz0cap : z0 ≤ (1-r)/2 := min_le_right _ _
        have hz : 0 ≤ z := le_max_left _ _
        have hzz0 : z ≤ z0 := max_le hz00 (by linarith)
        have hzS : z ≤ S := hzz0.trans hz0S
        have hzloss : z0-ζ ≤ z := le_max_right _ _
        have htarget : xi ν S-eps-ζ ≤ r+z := by
          have ht0 := le_max_left (xi ν S-S) (2*xi ν S-1)
          have ht1 := le_max_right (xi ν S-S) (2*xi ν S-1)
          change xi ν S-S ≤ inverseThreshold ν S at ht0
          change 2*xi ν S-1 ≤ inverseThreshold ν S at ht1
          have hmin : xi ν S-eps ≤ r+z0 := by
            dsimp [z0]
            rw [add_min]
            exact le_min (by linarith) (by linarith)
          linarith
        have hcredit := amplitude_credit hv.le hp hzS
        by_cases hzz : z = 0
        · rw [hzz] at htarget
          have hh := mul_le_mul_of_nonneg_left htarget hv.le
          nlinarith
        · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hzz)
          have hze : z = z0-ζ := by
            by_cases hz0 : 0 ≤ z0-ζ
            · exact max_eq_right hz0
            · exact False.elim (hzz (max_eq_left (le_of_not_ge hz0)))
          have hcap1 : r+2*z < 1 := by rw [hze]; linarith
          have hcap2 : 2*r+8*z < 3 := by linarith
          have hh := hIM z hz hzS hcap1 hcap2
          have ht := mul_le_mul_of_nonneg_left htarget hv.le
          nlinarith
      · have hmthreshold : plainThreshold ν S ≤ 2*m := by linarith
        let z0 := min S (2*(1-2*m)/9)
        let z := max 0 (z0-ζ)
        have hz00 : 0 ≤ z0 := le_min hS (by linarith)
        have hz0S : z0 ≤ S := min_le_left _ _
        have hz0cap : z0 ≤ 2*(1-2*m)/9 := min_le_right _ _
        have hz : 0 ≤ z := le_max_left _ _
        have hzz0 : z ≤ z0 := max_le hz00 (by linarith)
        have hzS : z ≤ S := hzz0.trans hz0S
        have hzloss : z0-ζ ≤ z := le_max_right _ _
        have htarget : xi ν S-ζ ≤ 2*m+z := by
          have ht0 := le_max_left (xi ν S-S) ((9*xi ν S-2)/7)
          have ht1 := le_max_right (xi ν S-S) ((9*xi ν S-2)/7)
          change xi ν S-S ≤ plainThreshold ν S at ht0
          change (9*xi ν S-2)/7 ≤ plainThreshold ν S at ht1
          have hmin : xi ν S ≤ 2*m+z0 := by
            dsimp [z0]
            rw [add_min]
            exact le_min (by linarith) (by linarith)
          linarith
        have hcredit := amplitude_credit hv.le hp hzS
        have hh := hPM z hz hzS (by linarith)
        have ht := mul_le_mul_of_nonneg_left htarget hv.le
        nlinarith
    · have hh : ν*xi ν S ≤ 2*ν*m := by nlinarith
      have hz : 0 ≤ ν*ζ := by positivity
      linarith
  · rw [max_eq_right (by linarith : 1 ≤ (1+5*r)/6)] at hI
    have hid := count_cutoff_identity (S:=S) hν1
    have ht := mul_le_mul_of_nonneg_left hr (show 0 ≤ 5/6-ν by linarith)
    have hz : 0 ≤ ν*ζ := by positivity
    nlinarith

end
end QRH.Record1252270103Source.NaturalLowDensity
