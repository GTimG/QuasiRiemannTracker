/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
True ordinary P4 prices on the early finite response/zero-band windows. -/
import Candidate.C092.transport.StrongPairRegularTerminalWindow

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.MediumReplace.Source
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness

/-- The actual P4 coefficient remains 2a-1. A stored certificate at lower
grid endpoints costs at most three grid steps on the genuine finite quota.
In particular no false eUpper<=nuActual guard is imposed on diagonal cells. -/
theorem terminal_ordinary_window_difference_approx
    {n y el eu ν ν₀ d m B r decrement rounding ε extra step price : ℝ}
    (hν0 : ν₀ ≤ ν+price) (hν : ν ≤ ν₀+step) (heu : eu ≤ el+step) (hs : 0 ≤ step) (hprice : 0 ≤ price)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hL : sourceWidth n y-(u:ℝ) ≤ 1)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hq : 0 ≤ nearOrdinaryQuota n B r-decrement)
    (hr0 : 0 ≤ rounding) (hr1 : rounding ≤ 1) :
    nearEscapeExponent n y eu ν d m B r decrement rounding ε extra ≤
      nearEscapeExponent n y el ν₀ d m B r decrement rounding ε extra+3*step+price*d*m := by
  let erased := max 0 (sourceWidth n y-(u:ℝ)-d*(nearOrdinaryQuota n B r-decrement)+rounding)
  have her0 : 0 ≤ erased := le_max_left _ _
  have her1 : erased ≤ 2 := by dsimp [erased]; apply max_le <;> nlinarith
  have hνgap : (ν-ν₀)*y ≤ step := by nlinarith [mul_le_mul (show ν-ν₀ ≤ step by linarith) hy1 hy0 hs]
  have heg : (eu-el)*erased ≤ 2*step := by
    have h1 := mul_le_mul_of_nonneg_right (show eu-el ≤ step by linarith) her0
    have h2 := mul_le_mul_of_nonneg_left her1 hs
    linarith
  have hn : -(price*d*m) ≤ (ν-ν₀)*(d*m) := by
    have h := mul_le_mul_of_nonneg_right (show -price ≤ ν-ν₀ by linarith) (mul_nonneg hd hm)
    nlinarith only [h]
  unfold nearEscapeExponent
  change _+eu*erased+extra ≤ _+el*erased+extra+3*step+price*d*m
  nlinarith

/-- Stored finite-window ordinary prices pay the actual same-zero P4
witness, with all radius/cap/slot losses and a stated early 3*step debit. -/
theorem terminal_ordinary_window_paid_approx {Label : Type*} {χ : Label→Character}
    {U a ε T allowance n y el eu ν ν₀ V d B r decrement rounding extra collar step price : ℝ} {i : ℕ}
    (c : Cutoff) (w : SupportedWitness χ (U^d) a ε (totalCutoff c) T allowance i)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (hel0 : 0 ≤ el) (hel1 : el ≤ (responseUpper:ℝ)) (hνlo : el ≤ ν₀) (hνhi : ν₀ ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c)
    (hc : y/(H:ℝ) ≤ (c.ordinary:ℝ)) (hc0 : sourceY0 ≤ (c.ordinary:ℝ))
    (hp : PaidWithBand y el ν₀ c) (hε : 0 ≤ ε) (hw : w.r < (c.inverse:ℝ))
    (hV : (98/100:ℝ) ≤ V) (hdV : V ≤ d) (hdc : d ≤ V+collar)
    (hr : (98/100:ℝ) ≤ r) (hrd : r ≤ min d (H:ℝ))
    (hB : collaredOrdinaryCap c w.m ≤ B) (hdec : 0 ≤ decrement) (hround : 0 ≤ rounding)
    (hν0 : ν₀ ≤ ν+price) (hν : ν ≤ ν₀+step) (heu : eu ≤ el+step) (hs : 0 ≤ step) (hprice : 0 ≤ price)
    (hL : sourceWidth n y-(u:ℝ) ≤ 1) (hq : 0 ≤ nearOrdinaryQuota n B r-decrement) (hr1 : rounding ≤ 1)
    (hfees : collar+(15/4)*d*ε+
      el*(d*((5/4:ℝ)*(min d (H:ℝ)-r)+(3/4:ℝ)*(B-collaredOrdinaryCap c w.m))+
        d*decrement+rounding)+extra+3*step+price*d*w.m ≤ (3/4)*(rho:ℝ)) :
    nearEscapeExponent n y eu ν d w.m B r decrement rounding ε extra <
      V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V) := by
  have hpay := near_escape_paid (ν:=ν₀) (e:=el) (extra:=extra+3*step+price*d*w.m) c w hy0 hy1 hyn hn
    hel0 hel1 hνlo hνhi hg hc hc0 hp hε hw hV hdV hdc hr hrd hB hdec hround
    (by linarith)
  have hwin := terminal_ordinary_window_difference_approx (m:=w.m) (B:=B) (r:=r) (n:=n)
    (el:=el) (ν₀:=ν₀) (ε:=ε) (extra:=extra) hν0 hν heu hs hprice
    (source_domain.1.le.trans hy0) (hy1.trans (by norm_num [sourceY])) hL
    (show 0 ≤ d by linarith) w.plain_length_lower hq hround hr1
  unfold nearEscapeExponent at hwin hpay ⊢
  linarith

#print axioms terminal_ordinary_window_difference_approx
#print axioms terminal_ordinary_window_paid_approx
end
end QRH.Cycle092.StrongPair
