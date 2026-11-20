/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual P4 ordinary debit, rounded earlier quota and ONE conductor collar. -/
import Candidate.C092.transport.StrongPairLowMeasured
import Candidate.C092.transport.SourceFurtherWitness
import Candidate.C092.transport.WitnessConductorBank

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.MediumReplace.Source
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness

/-- Rounding a dominating witness cap upward costs at most three quarters
of its displacement in the true native/earlier frozen source capacity.
The jump from the negative source gain at Y to zero is favorable. -/
theorem frozen_capacity_rounding {n m B : ℝ}
    (hm0 : sourceY0 ≤ m) (hmB : m ≤ B) :
    frozenCapacity n m-frozenCapacity n B ≤ (3/4:ℝ)*(B-m) := by
  unfold frozenCapacity
  by_cases hmY : m ≤ sourceY
  · by_cases hBY : B ≤ sourceY
    · rw [continuedGain,ite_eq_left hmY,continuedGain,ite_eq_left hBY]
      have h := sourceGain_quarter_secant hm0 hmB hBY
      linarith
    · rw [continuedGain,ite_eq_left hmY,continuedGain,ite_eq_right hBY]
      have h := sourceGain_quarter_secant hm0 hmY (le_refl sourceY)
      rw [source_native_value] at h
      have hYB : sourceY ≤ B := le_of_not_ge hBY
      linarith
  · have hBY : ¬B ≤ sourceY := fun h=>hmY (hmB.trans h)
    rw [continuedGain,ite_eq_right hmY,continuedGain,ite_eq_right hBY]
    linarith

/-- This is the actual exponent after P4 and whole-slot erasure. m remains
the true witness length; B is only an upper source cap. -/
def ordinaryEscapeExponent (n y e ν d m B decrement rounding ε extra : ℝ) : ℝ :=
  d+ν*(y-d*m)+3*d*ε+
    e*max 0 (sourceWidth n y-(u:ℝ)-d*(frozenCapacity n B-decrement)+rounding)+extra

/-- All source-cap rounding and decrement losses are charged explicitly in
addition to the true collared price. No actual witness length is substituted. -/
theorem ordinary_exponent_vs_collared {n y e ν d m B decrement rounding ε extra : ℝ}
    (c : Cutoff) (hd : (H:ℝ) < d) (he : 0 ≤ e)
    (hm0 : sourceY0 ≤ collaredOrdinaryCap c m)
    (hB : collaredOrdinaryCap c m ≤ B) (hdec : 0 ≤ decrement) (hround : 0 ≤ rounding) :
    ordinaryEscapeExponent n y e ν d m B decrement rounding ε extra ≤
      d+collaredOrdinaryPrice n y e ν d m ε c+d*ε+
        e*(d*((3/4:ℝ)*(B-collaredOrdinaryCap c m))+d*decrement+rounding)+extra := by
  have hdp : 0 ≤ d := H_real_bounds.1.le.trans hd.le
  have hcap := frozen_capacity_rounding (n:=n) hm0 hB
  have hscale := mul_le_mul_of_nonneg_left hcap hdp
  let fee : ℝ := d*((3/4:ℝ)*(B-collaredOrdinaryCap c m))+d*decrement+rounding
  have hfee : 0 ≤ fee := by dsimp [fee]; positivity
  have hmax : max 0 (sourceWidth n y-(u:ℝ)-d*(frozenCapacity n B-decrement)+rounding) ≤
      max 0 (sourceWidth n y-(u:ℝ)-d*frozenCapacity n (collaredOrdinaryCap c m))+fee := by
    apply max_le
    · linarith [le_max_left 0 (sourceWidth n y-(u:ℝ)-d*frozenCapacity n (collaredOrdinaryCap c m))]
    · dsimp [fee]
      linarith [le_max_right 0 (sourceWidth n y-(u:ℝ)-d*frozenCapacity n (collaredOrdinaryCap c m))]
  have hcol : collaredOrdinaryPrice n y e ν d m ε c =
      ν*(y-d*m)+2*d*ε+e*max 0 (sourceWidth n y-(u:ℝ)-d*frozenCapacity n (collaredOrdinaryCap c m)) := by
    unfold collaredOrdinaryPrice actualOrdinaryPrice
    rw [ite_eq_right (not_le_of_gt hd)]
    unfold frozenOrdinaryPrice
    ring
  rw [hcol]
  unfold ordinaryEscapeExponent
  have hh := mul_le_mul_of_nonneg_left hmax he
  dsimp [fee] at hh
  linarith

/-- The real witness's inverse escape and scalar certificate pay the full
ordinary energy exponent. The conductor excess d-V is paid ONCE, using the
actual bank inequality d+radialAllowance(d)<=V+radialAllowance(V)+collar. -/
theorem ordinary_escape_paid {Label : Type*} {χ : Label→Character}
    {U a ε T allowance n y e ν V d B decrement rounding extra collar : ℝ} {i : ℕ}
    (c : Cutoff) (w : SupportedWitness χ (U^d) a ε (totalCutoff c) T allowance i)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ)) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c)
    (hc : y/(H:ℝ) ≤ (c.ordinary:ℝ)) (hc0 : sourceY0 ≤ (c.ordinary:ℝ))
    (hp : PaidWithBand y e ν c) (hε : 0 ≤ ε) (hr : w.r < (c.inverse:ℝ))
    (hV : (H:ℝ) ≤ V) (hdV : V ≤ d) (hdH : (H:ℝ) < d) (hdc : d ≤ V+collar)
    (hB : collaredOrdinaryCap c w.m ≤ B) (hdec : 0 ≤ decrement) (hround : 0 ≤ rounding)
    (hfees : collar+(15/4)*d*ε+
      e*(d*((3/4:ℝ)*(B-collaredOrdinaryCap c w.m))+d*decrement+rounding)+extra ≤ (3/4)*(rho:ℝ)) :
    ordinaryEscapeExponent n y e ν d w.m B decrement rounding ε extra <
      V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V) := by
  have hd98 : (98/100:ℝ) ≤ d := (by norm_num [H,u] : (98/100:ℝ) ≤ (H:ℝ)).trans (hV.trans hdV)
  have hpaid := actual_ordinary_price_paid c w hy hn he0 he1 hν hν1 hg hc hc0 hp hε hr hd98
  have hm0 : sourceY0 ≤ collaredOrdinaryCap c w.m := hc0.trans (le_max_right _ _)
  have hraw := ordinary_exponent_vs_collared (n:=n) (y:=y) (ν:=ν) (ε:=ε) (extra:=extra) c hdH he0 hm0 hB hdec hround
  have hbank := enlarged_price hdV hdc
  unfold radialAllowance at hpaid hbank
  push_cast at hpaid hbank
  linarith

#print axioms frozen_capacity_rounding
#print axioms ordinary_escape_paid
end
end QRH.Cycle092.StrongPair
