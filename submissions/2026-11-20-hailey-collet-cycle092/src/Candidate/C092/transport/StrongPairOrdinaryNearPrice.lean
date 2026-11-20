/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The all-radii ordinary price from the actual restored finite source bank. -/
import Candidate.C092.transport.StrongPairOrdinaryNearSlope

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.MediumReplace.Source
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness

def nearEscapeExponent (n y e ν d m B r decrement rounding ε extra : ℝ) : ℝ :=
  d+ν*(y-d*m)+3*d*ε+
    e*max 0 (sourceWidth n y-(u:ℝ)-d*(nearOrdinaryQuota n B r-decrement)+rounding)+extra

theorem near_exponent_vs_collared {n y e ν d m B r decrement rounding ε extra : ℝ}
    (c : Cutoff) (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hm : y/(H:ℝ) ≤ (c.ordinary:ℝ))
    (hd : (98/100:ℝ) ≤ d) (hr : (98/100:ℝ) ≤ r) (hrd : r ≤ min d (H:ℝ))
    (hB : collaredOrdinaryCap c m ≤ B) (hdec : 0 ≤ decrement) (hround : 0 ≤ rounding) :
    nearEscapeExponent n y e ν d m B r decrement rounding ε extra ≤
      d+collaredOrdinaryPrice n y e ν d m ε c+d*ε+
        e*(d*((5/4:ℝ)*(min d (H:ℝ)-r)+(3/4:ℝ)*(B-collaredOrdinaryCap c m))+
          d*decrement+rounding)+extra := by
  have hcap := near_capacity_payment hn hy0 hy1 hyn (hm.trans (le_max_right _ _)) hB hd hr hrd
  change ordinaryCapacity n (collaredOrdinaryCap c m) d-d*nearOrdinaryQuota n B r ≤
    d*((5/4:ℝ)*(min d (H:ℝ)-r)+(3/4:ℝ)*(B-collaredOrdinaryCap c m)) at hcap
  let fee : ℝ := d*((5/4:ℝ)*(min d (H:ℝ)-r)+(3/4:ℝ)*(B-collaredOrdinaryCap c m))+d*decrement+rounding
  have hd0 : 0 ≤ d := by linarith
  have hfee : 0 ≤ fee := by dsimp [fee]; positivity
  have hmax : max 0 (sourceWidth n y-(u:ℝ)-d*(nearOrdinaryQuota n B r-decrement)+rounding) ≤
      max 0 (sourceWidth n y-(u:ℝ)-ordinaryCapacity n (collaredOrdinaryCap c m) d)+fee := by
    apply max_le
    · linarith [le_max_left 0 (sourceWidth n y-(u:ℝ)-ordinaryCapacity n (collaredOrdinaryCap c m) d)]
    · dsimp [fee]
      linarith [le_max_right 0 (sourceWidth n y-(u:ℝ)-ordinaryCapacity n (collaredOrdinaryCap c m) d)]
  have hcol : collaredOrdinaryPrice n y e ν d m ε c =
      ν*(y-d*m)+2*d*ε+e*max 0 (sourceWidth n y-(u:ℝ)-ordinaryCapacity n (collaredOrdinaryCap c m) d) := by
    rw [collaredOrdinaryPrice,actualOrdinaryPrice_as_capacity]
    ring
  rw [hcol]
  unfold nearEscapeExponent
  have hh := mul_le_mul_of_nonneg_left hmax he
  dsimp [fee] at hh
  linarith

theorem near_escape_paid {Label : Type*} {χ : Label→Character}
    {U a ε T allowance n y e ν V d B r decrement rounding extra collar : ℝ} {i : ℕ}
    (c : Cutoff) (w : SupportedWitness χ (U^d) a ε (totalCutoff c) T allowance i)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ)) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c)
    (hc : y/(H:ℝ) ≤ (c.ordinary:ℝ)) (hc0 : sourceY0 ≤ (c.ordinary:ℝ))
    (hp : PaidWithBand y e ν c) (hε : 0 ≤ ε) (hw : w.r < (c.inverse:ℝ))
    (hV : (98/100:ℝ) ≤ V) (hdV : V ≤ d) (hdc : d ≤ V+collar)
    (hr : (98/100:ℝ) ≤ r) (hrd : r ≤ min d (H:ℝ))
    (hB : collaredOrdinaryCap c w.m ≤ B) (hdec : 0 ≤ decrement) (hround : 0 ≤ rounding)
    (hfees : collar+(15/4)*d*ε+
      e*(d*((5/4:ℝ)*(min d (H:ℝ)-r)+(3/4:ℝ)*(B-collaredOrdinaryCap c w.m))+
        d*decrement+rounding)+extra ≤ (3/4)*(rho:ℝ)) :
    nearEscapeExponent n y e ν d w.m B r decrement rounding ε extra <
      V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V) := by
  have hd : (98/100:ℝ) ≤ d := hV.trans hdV
  have hpaid := actual_ordinary_price_paid c w hy1 hn he0 he1 hν hν1 hg hc hc0 hp hε hw hd
  have hraw := near_exponent_vs_collared (n:=n) (y:=y) (ν:=ν) (ε:=ε) (extra:=extra)
    c hy0 hy1 hyn hn he0 hc hd hr hrd hB hdec hround
  have hbank := enlarged_price hdV hdc
  unfold radialAllowance at hpaid hbank
  push_cast at hpaid hbank
  linarith

#print axioms near_escape_paid
end
end QRH.Cycle092.StrongPair
