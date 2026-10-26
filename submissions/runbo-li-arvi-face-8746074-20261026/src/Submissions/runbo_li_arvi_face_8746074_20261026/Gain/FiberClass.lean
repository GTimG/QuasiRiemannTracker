import Submissions.runbo_li_arvi_face_8746074_20261026.Gain.Gain

/-!
# Per-class fiber exponent (Lemma B_K, normalized ambient exponent `Q = 1`)

Class `p ∈ [0,1/2]`, `K` copies of the marked slots, detector root `x` with cutoff
`t = invThr + plainThr/2` and balance `6 ν x + (5 - 6 ν) t = 5`.
Primitive count gates (from the moment estimates):
* long inverse: `E ≤ max 1 ((1+5r)/6) - ν r + loss`,
* plain (unmarked): `E ≤ 1 - 2 ν m + loss`,
* marked inverse with repeated slots: for `0 ≤ z ≤ K S`, `r + 2z < 1`, `2r + 8z < 3`,
  `E ≤ 1 - ν r - 2 ν p z + loss`,
* marked plain: for `0 ≤ z ≤ S`, `z ≤ h`, `2m + lam z ≤ B`, `E ≤ 1 - 2ν m - 2ν p z + loss`.
Conclusion: `E ≤ 1 - ν x + losses`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.RepeatedMarks
noncomputable section


theorem fiber_exponent_class {ν B lam h x t p K S r m E loss eps zeta : ℝ}
    (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hlam : 1 < lam) (hh : 0 ≤ h)
    (hx0 : 5/6 ≤ x) (hxB : x ≤ B) (hB : B ≤ 1)
    (hbalance : 6*ν*x + (5-6*ν)*t = 5)
    (hcut : t = invThr p K x S 1 + plainThr p B lam h x S 1/2)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hK : 1 ≤ K) (hS : 0 ≤ S)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/100) (hzeta : 0 < zeta)
    (hlen : t - eps ≤ r + m) (hr : r ≤ t + eps)
    (hI : E ≤ max 1 ((1+5*r)/6) - ν*r + loss)
    (hP : E ≤ 1 - 2*ν*m + loss)
    (hIM : ∀ z : ℝ, 0 ≤ z → z ≤ K*S → r + 2*z < 1 → 2*r + 8*z < 3 →
      E ≤ 1 - ν*r - 2*ν*p*z + loss)
    (hPM : ∀ z : ℝ, 0 ≤ z → z ≤ S → z ≤ h → 2*m + lam*z ≤ B →
      E ≤ 1 - 2*ν*m - 2*ν*p*z + loss) :
    E ≤ 1 - ν*x + loss + eps + ν*zeta := by
  have hv : 0 < ν := by linarith
  have hx : x ≤ 1 := hxB.trans hB
  have hl : 0 < lam := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hKS : 0 ≤ K*S := mul_nonneg (by linarith) hS
  by_cases hr1 : r ≤ 1
  · rw [max_eq_left (by linarith : (1+5*r)/6 ≤ 1)] at hI
    by_cases hmB : 2*m ≤ B
    · -- the same-zero alternative
      by_cases hinv : invThr p K x S 1 - eps ≤ r
      · -- inverse branch with repeated slots
        let z0 := min (K*S) ((1-r)/2)
        let z := max 0 (z0 - zeta)
        have hz00 : 0 ≤ z0 := le_min hKS (by linarith)
        have hz0S : z0 ≤ K*S := min_le_left _ _
        have hz0cap : z0 ≤ (1-r)/2 := min_le_right _ _
        have hz : 0 ≤ z := le_max_left _ _
        have hzz0 : z ≤ z0 := max_le hz00 (by linarith)
        have hzS : z ≤ K*S := hzz0.trans hz0S
        have hzloss : z0 - zeta ≤ z := le_max_right _ _
        -- target: r + 2 p z0 ≥ x - eps (from the two inverse thresholds)
        have ht0 : x - 2*p*K*S ≤ invThr p K x S 1 := le_max_left _ _
        have ht1 : (x - p*1)/(1-p) ≤ invThr p K x S 1 := le_max_right _ _
        have ht1' : x - p ≤ (1-p)*(r + eps) := by
          have := (div_le_iff₀ h1p).mp (ht1.trans (by linarith : invThr p K x S 1 ≤ r + eps))
          linarith
        have hpe : 0 ≤ p*eps := mul_nonneg hp0 heps
        have hpr : p*r = p*r := rfl
        have ht1e : x - p ≤ r + eps - p*r - p*eps := by
          have := ht1'; ring_nf at this ⊢; linarith
        have htarget0 : x - eps ≤ r + 2*p*z0 := by
          rcases le_total (K*S) ((1-r)/2) with hc | hc
          · have : z0 = K*S := min_eq_left hc
            rw [this]; linarith
          · have : z0 = (1-r)/2 := min_eq_right hc
            rw [this]
            have e : r + 2*p*((1-r)/2) = r + p - p*r := by ring
            rw [e]; linarith
        have htarget : x - eps - 2*p*zeta ≤ r + 2*p*z := by
          have h1 := mul_le_mul_of_nonneg_left hzloss (by linarith : (0:ℝ) ≤ 2*p)
          have e : 2*p*(z0 - zeta) = 2*p*z0 - 2*p*zeta := by ring
          linarith
        -- admissions: r ≥ 2x - 1 - eps
        have hr23 : 2*x - 1 - eps ≤ r := by
          have hk : 0 ≤ (1-x)*(1-2*p) := mul_nonneg (by linarith) (by linarith)
          have e : x - p - (2*x-1)*(1-p) = (1-x)*(1-2*p) := by ring
          -- (1-p)(r + eps - (2x-1)) ≥ 0
          have h3 : 0 ≤ (1-p)*(r + eps - (2*x-1)) := by
            have := ht1'; nlinarith
          have h4 : 0 ≤ r + eps - (2*x-1) := by
            by_contra hneg; push Not at hneg
            have := mul_neg_of_pos_of_neg h1p hneg; linarith
          linarith
        have hpz : 0 ≤ ν*(2*p*zeta) := by positivity
        have hpz' : ν*(2*p*zeta) ≤ ν*zeta := by
          apply mul_le_mul_of_nonneg_left _ hv.le; nlinarith
        by_cases hzz : z = 0
        · rw [hzz] at htarget
          have ht := mul_le_mul_of_nonneg_left htarget hv.le
          have hIr : E ≤ 1 - ν*r + loss := by linarith
          have hve : ν*eps ≤ eps := by nlinarith
          nlinarith
        · have hze : z = z0 - zeta := by
            by_cases hz0 : 0 ≤ z0 - zeta
            · exact max_eq_right hz0
            · exact False.elim (hzz (max_eq_left (le_of_not_ge hz0)))
          have hcap1 : r + 2*z < 1 := by rw [hze]; linarith
          have hcap2 : 2*r + 8*z < 3 := by
            have : 8*z ≤ 4*(1-r) := by rw [hze]; linarith
            linarith
          have hc := hIM z hz hzS hcap1 hcap2
          have ht := mul_le_mul_of_nonneg_left htarget hv.le
          have hve : ν*eps ≤ eps := by nlinarith
          have e1 : ν*(x - eps - 2*p*zeta) = ν*x - ν*eps - ν*(2*p*zeta) := by ring
          have e2 : ν*(r + 2*p*z) = ν*r + 2*ν*p*z := by ring
          linarith
      · -- plain branch
        have hmt : plainThr p B lam h x S 1 ≤ 2*m := by linarith
        let z := min S (min h ((B - 2*m)/lam))
        have hz : 0 ≤ z := le_min hS (le_min hh (div_nonneg (by linarith) hl.le))
        have hzS : z ≤ S := min_le_left _ _
        have hzh : z ≤ h := (min_le_right _ _).trans (min_le_left _ _)
        have hzc : z ≤ (B - 2*m)/lam := (min_le_right _ _).trans (min_le_right _ _)
        have hzcap : 2*m + lam*z ≤ B := by
          have := (le_div_iff₀ hl).mp hzc; nlinarith
        -- target: 2m + 2 p z ≥ x
        have hd : 0 < 1 - 2*p/lam := by rw [sub_pos, div_lt_one hl]; linarith
        have hm0 : x - 2*p*S ≤ 2*m := (le_max_left _ _).trans hmt
        have hm1 : x - 2*p*h*1 ≤ 2*m := ((le_max_left _ _).trans (le_max_right _ _)).trans hmt
        have hm2 : (x - 2*p*B*1/lam)/(1 - 2*p/lam) ≤ 2*m :=
          ((le_max_right _ _).trans (le_max_right _ _)).trans hmt
        have htarget : x ≤ 2*m + 2*p*z := by
          have h2p : 0 ≤ 2*p := by linarith
          rcases le_total S (min h ((B - 2*m)/lam)) with hc | hc
          · have : z = S := min_eq_left hc
            rw [this]; linarith
          · have hz' : z = min h ((B - 2*m)/lam) := min_eq_right hc
            rcases le_total h ((B - 2*m)/lam) with hc2 | hc2
            · rw [hz', min_eq_left hc2]; linarith
            · rw [hz', min_eq_right hc2]
              have h3 := (div_le_iff₀ hd).mp hm2
              have e : 2*p*((B - 2*m)/lam) = 2*p*B/lam - 2*m*(2*p/lam) := by field_simp
              have h3' : x - 2*p*B/lam ≤ 2*m - 2*m*(2*p/lam) := by
                have e2 : 2*m*(1 - 2*p/lam) = 2*m - 2*m*(2*p/lam) := by ring
                have e3 : x - 2*p*B*1/lam = x - 2*p*B/lam := by ring
                linarith
              linarith
        have hc := hPM z hz hzS hzh hzcap
        have ht := mul_le_mul_of_nonneg_left htarget hv.le
        have hzz : 0 ≤ ν*zeta := by positivity
        nlinarith
    · have ht : ν*x ≤ 2*ν*m := by nlinarith
      have hzz : 0 ≤ ν*zeta := by positivity
      linarith
  · -- long inverse branch
    rw [max_eq_right (by linarith : 1 ≤ (1+5*r)/6)] at hI
    have ht := mul_le_mul_of_nonneg_left hr (show 0 ≤ 5/6 - ν by linarith)
    have hzz : 0 ≤ ν*zeta := by positivity
    nlinarith

end
end QRH.RepeatedMarks
