/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
True ordinary P4 prices on the early finite response/zero-band windows. -/
import Candidate.C092.transport.StrongPairOrdinaryNearHetero

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.MediumReplace.Source
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness

/-- The actual P4 coefficient remains 2a-1. A stored certificate at lower
grid endpoints costs at most three grid steps on the genuine finite quota.
In particular no false eUpper<=nuActual guard is imposed on diagonal cells. -/
theorem terminal_ordinary_window_difference
    {n y el eu ν ν₀ d m B r decrement rounding ε extra step : ℝ}
    (hν0 : ν₀ ≤ ν) (hν : ν ≤ ν₀+step) (heu : eu ≤ el+step) (hs : 0 ≤ step)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hL : sourceWidth n y-(u:ℝ) ≤ 1)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hq : 0 ≤ nearOrdinaryQuota n B r-decrement)
    (hr0 : 0 ≤ rounding) (hr1 : rounding ≤ 1) :
    nearEscapeExponent n y eu ν d m B r decrement rounding ε extra ≤
      nearEscapeExponent n y el ν₀ d m B r decrement rounding ε extra+3*step := by
  let erased := max 0 (sourceWidth n y-(u:ℝ)-d*(nearOrdinaryQuota n B r-decrement)+rounding)
  have her0 : 0 ≤ erased := le_max_left _ _
  have her1 : erased ≤ 2 := by dsimp [erased]; apply max_le <;> nlinarith
  have hνgap : (ν-ν₀)*y ≤ step := by nlinarith [mul_le_mul (show ν-ν₀ ≤ step by linarith) hy1 hy0 hs]
  have heg : (eu-el)*erased ≤ 2*step := by
    have h1 := mul_le_mul_of_nonneg_right (show eu-el ≤ step by linarith) her0
    have h2 := mul_le_mul_of_nonneg_left her1 hs
    linarith
  have hn : 0 ≤ (ν-ν₀)*(d*m) := mul_nonneg (sub_nonneg.mpr hν0) (mul_nonneg hd hm)
  unfold nearEscapeExponent
  change _+eu*erased+extra ≤ _+el*erased+extra+3*step
  nlinarith

/-- Stored finite-window ordinary prices pay the actual same-zero P4
witness, with all radius/cap/slot losses and a stated early 3*step debit. -/
theorem terminal_ordinary_window_paid {Label : Type*} {χ : Label→Character}
    {U a ε T allowance n y el eu ν ν₀ V d B r decrement rounding extra collar step : ℝ} {i : ℕ}
    (c : Cutoff) (w : SupportedWitness χ (U^d) a ε (totalCutoff c) T allowance i)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (hel0 : 0 ≤ el) (hel1 : el ≤ (responseUpper:ℝ)) (hνlo : el ≤ ν₀) (hνhi : ν₀ ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c)
    (hc : y/(H:ℝ) ≤ (c.ordinary:ℝ)) (hc0 : sourceY0 ≤ (c.ordinary:ℝ))
    (hp : PaidWithBand y el ν₀ c) (hε : 0 ≤ ε) (hw : w.r < (c.inverse:ℝ))
    (hV : (98/100:ℝ) ≤ V) (hdV : V ≤ d) (hdc : d ≤ V+collar)
    (hr : (98/100:ℝ) ≤ r) (hrd : r ≤ min d (H:ℝ))
    (hB : collaredOrdinaryCap c w.m ≤ B) (hdec : 0 ≤ decrement) (hround : 0 ≤ rounding)
    (hν0 : ν₀ ≤ ν) (hν : ν ≤ ν₀+step) (heu : eu ≤ el+step) (hs : 0 ≤ step)
    (hL : sourceWidth n y-(u:ℝ) ≤ 1) (hq : 0 ≤ nearOrdinaryQuota n B r-decrement) (hr1 : rounding ≤ 1)
    (hfees : collar+(15/4)*d*ε+
      el*(d*((5/4:ℝ)*(min d (H:ℝ)-r)+(3/4:ℝ)*(B-collaredOrdinaryCap c w.m))+
        d*decrement+rounding)+extra+3*step ≤ (3/4)*(rho:ℝ)) :
    nearEscapeExponent n y eu ν d w.m B r decrement rounding ε extra <
      V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V) := by
  have hpay := near_escape_paid (ν:=ν₀) (e:=el) (extra:=extra+3*step) c w hy0 hy1 hyn hn
    hel0 hel1 hνlo hνhi hg hc hc0 hp hε hw hV hdV hdc hr hrd hB hdec hround
    (by linarith)
  have hwin := terminal_ordinary_window_difference (m:=w.m) (B:=B) (r:=r) (n:=n)
    (el:=el) (ν₀:=ν₀) (ε:=ε) (extra:=extra) hν0 hν heu hs
    (source_domain.1.le.trans hy0) (hy1.trans (by norm_num [sourceY])) hL
    (show 0 ≤ d by linarith) w.plain_length_lower hq hround hr1
  unfold nearEscapeExponent at hwin hpay ⊢
  linarith

theorem terminal_ordinary_window_fee {M conductor gap ε εsource buffer τ d e B mbar radiusGap dec rounding collar step : ℝ}
    {K degree : ℕ}
    (hM : 0 ≤ M) (hd0 : 0 ≤ d) (hd : d ≤ M)
    (he : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hg : 0 ≤ gap) (hgap0 : 0 ≤ B-mbar) (hgap : B-mbar ≤ gap)
    (hRad0 : 0 ≤ radiusGap) (hRad : radiusGap ≤ gap)
    (hdec0 : 0 ≤ dec) (hdec : dec ≤ gap) (hr0 : 0 ≤ rounding) (hr : rounding ≤ gap)
    (hε : 0 ≤ ε) (hs : 0 ≤ εsource)
    (hcollar : collar ≤ 3*conductor) (hc : 3*conductor ≤ (rho:ℝ)/128)
    (hcap : (responseUpper:ℝ)*(M*(2*gap)+M*gap+gap) ≤ (rho:ℝ)/128)
    (hwit : (15/4:ℝ)*M*ε ≤ (rho:ℝ)/128) (hsource : M*εsource ≤ (rho:ℝ)/128)
    (hbuffer : buffer*(K:ℝ) ≤ (rho:ℝ)/128) (hheight : τ*(degree:ℝ) ≤ (rho:ℝ)/128)
    (hstep : step ≤ (rho:ℝ)/128) :
    collar+(15/4:ℝ)*d*ε+e*(d*((5/4:ℝ)*radiusGap+(3/4:ℝ)*(B-mbar))+d*dec+rounding)+
      (d*εsource+buffer*(K:ℝ)+τ*(degree:ℝ))+3*step ≤ (3/4:ℝ)*(rho:ℝ) := by
  have hE : (0:ℝ) ≤ (responseUpper:ℝ) := by norm_num [responseUpper]
  have hcap' : e*(d*((5/4:ℝ)*radiusGap+(3/4:ℝ)*(B-mbar))+d*dec+rounding) ≤
      (responseUpper:ℝ)*(M*(2*gap)+M*gap+gap) := by
    apply mul_le_mul he1 _ (by positivity) hE
    have hdelta : (5/4:ℝ)*radiusGap+(3/4:ℝ)*(B-mbar) ≤ 2*gap := by linarith
    have h1 := mul_le_mul hd hdelta (by positivity) hM
    have h2 := mul_le_mul hd hdec hdec0 hM
    linarith
  have hwit' : (15/4:ℝ)*d*ε ≤ (15/4:ℝ)*M*ε := by gcongr
  have hsource' : d*εsource ≤ M*εsource := by gcongr
  have hrho : (0:ℝ) ≤ (rho:ℝ) := by norm_num [rho]
  linarith

#print axioms terminal_ordinary_window_fee
#print axioms terminal_ordinary_window_paid
end
end QRH.Cycle092.StrongPair
