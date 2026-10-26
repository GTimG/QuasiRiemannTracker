import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.TerminalLedger
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The direct deletion of a LOW child into the old region is paid by the amplifier width, the first-level surplus and the
saving of its second common part. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section

/-- The exponent of a deletion paid at the rate `rate`, for a child whose overshoot `F` is at most `G + padding` with
`rate G <= a + X - reserve`, exceeds the amplifier width `a` by at most the allowance `X` less the reserve. -/
theorem direct_deletion_paid_bound {d δ F G padding rate a X reserve : ℝ} (hd : d ≤ δ) (hδ : 0 ≤ δ)
    (hrate : 0 ≤ rate ∧ rate ≤ 1) (hpad : 0 ≤ padding) (hG : 0 ≤ G) (hF : F ≤ G + padding)
    (hpay : rate * G ≤ a + X - reserve) :
    d + rate * max (F - d) 0 - δ - a ≤ X - reserve + rate * padding := by
  have h1 := Cycle63.Physical.paid_deletion_bound (F := F) hd hδ hrate
  have h2 : max F 0 ≤ G + padding := max_le hF (by linarith)
  have h3 := mul_le_mul_of_nonneg_left h2 hrate.1
  linarith

/-- The first-level surplus `max (3 c - 5 d - R) 0 / 6` and the extraction `min c d` pay `κq` times the excess
`max (c - d) 0` of the own first ideal over the other one, when `κq <= 1/2` and the active radical `R` is at most `d`. -/
theorem b_sigma_reserve {κq c d R : ℝ} (hκq : 0 ≤ κq) (hκq2 : κq ≤ 1 / 2) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hRd : R ≤ d) :
    κq * max (c - d) 0 ≤ max (3 * c - 5 * d - R) 0 / 6 + κq * min c d := by
  have hm0 : 0 ≤ max (3 * c - 5 * d - R) 0 / 6 := by positivity
  rcases le_total c d with h | h
  · rw [max_eq_right (show c - d ≤ 0 by linarith)]
    have := mul_nonneg hκq (le_min hc hd)
    linarith
  · rw [max_eq_left (show (0 : ℝ) ≤ c - d by linarith), min_eq_right h]
    by_cases h2 : 2 * d ≤ c
    · have h3 : (c - 2 * d) / 2 ≤ max (3 * c - 5 * d - R) 0 / 6 := by
        have := le_max_left (3 * c - 5 * d - R) 0
        linarith
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - κq by linarith) (show (0 : ℝ) ≤ c - 2 * d by linarith)]
    · nlinarith [mul_nonneg hκq (show (0 : ℝ) ≤ 2 * d - c by linarith)]

/-- The reserve `a + B_sigma + (s - p2) - κq F⁺ - L` of the direct deletion of a child is nonnegative when the width
reduction `max (c - d) 0 + g - t` is large: the overshoot is `F = gbar + 6 a + ω - Red`, the extraction is
`Red = min c d + (s - g) + t + r + κ6 f`, the surplus `B_sigma = max (3 c - 5 d - R) 0 / 6`, and `vN` is the width of the
squarefree nonunit primes. -/
theorem direct_deletion_slack_nonneg {κq a gbar ω L c d R s p₂ g t vN r f κ6 : ℝ}
    (hκq : 0 ≤ κq) (hκq2 : κq ≤ 1 / 2) (hκ6 : 0 ≤ κ6) (hr : 0 ≤ r) (hf : 0 ≤ f)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hRd : R ≤ d) (hsp : p₂ ≤ s) (hL : L ≤ a)
    (hprime : κq * (g - t - vN) ≤ (s - p₂) + κq * ((s - g) + t))
    (hsel : (κq * (gbar + 6 * a) - a) + κq * ω + L ≤ κq * (max (c - d) 0 + g - t - vN)) :
    0 ≤ a + max (3 * c - 5 * d - R) 0 / 6 + (s - p₂) -
      κq * max (gbar + 6 * a + ω - (min c d + (s - g) + t + r + κ6 * f)) 0 - L := by
  have hi := b_sigma_reserve hκq hκq2 hc hd hRd
  have hB0 : 0 ≤ max (3 * c - 5 * d - R) 0 / 6 := by positivity
  by_cases hF : gbar + 6 * a + ω - (min c d + (s - g) + t + r + κ6 * f) ≤ 0
  · rw [max_eq_right hF]
    linarith
  · rw [max_eq_left (not_le.mp hF).le]
    have hrf : 0 ≤ κq * (r + κ6 * f) := mul_nonneg hκq (add_nonneg hr (mul_nonneg hκ6 hf))
    nlinarith [hi, hprime, hsel, hrf]

/-- A child of width `M1 = 1 - 6 a - v - ω` whose width reduction `v` exceeds `1 - 6 a - M⋆` and whose squarefree
nonunit primes fit in its width has the width reduction needed by `direct_deletion_slack_nonneg`, when the deficit `D0`
of the deletion at zero extraction and the loss `L` are below `κq (1 - 6 a - 2 M⋆)`. -/
theorem direct_deletion_selection {κq a gbar ω L Mstar v vN M1 : ℝ} (hκq : 0 ≤ κq)
    (hM1 : M1 = 1 - 6 * a - v - ω) (hvN : vN ≤ M1) (hv : 1 - 6 * a - Mstar < v)
    (hnum : (κq * (gbar + 6 * a) - a) + L ≤ κq * (1 - 6 * a - 2 * Mstar)) :
    (κq * (gbar + 6 * a) - a) + κq * ω + L ≤ κq * (v - vN) := by
  have h1 : κq * (v - M1) ≤ κq * (v - vN) := mul_le_mul_of_nonneg_left (by linarith) hκq
  have h2 : κq * (2 * (1 - 6 * a - Mstar) - (1 - 6 * a - ω)) ≤ κq * (v - M1) :=
    mul_le_mul_of_nonneg_left (by rw [hM1]; linarith) hκq
  nlinarith [h1, h2, hnum]

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
