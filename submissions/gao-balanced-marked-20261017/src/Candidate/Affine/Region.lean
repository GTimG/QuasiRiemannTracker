/- Copyright (c) 2026. Released under Apache 2.0. -/
import Candidate.Affine.Certificates

/-! Consequences of the region certificates: the new cutoff is admissible,
the crossing lies in the inverse range, the affine window contains the
crossing plain length, the old plain tail is dominated, the new count is
below the old count at `kappaStar`, and the new row closes at `theta`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace DetectorAffine
noncomputable section
open Cycle63.Arithmetic.Bernstein

/-- `kappaStar = 2*theta-1` at theta = 21871/25000. -/
def kStar : ℝ := 9371/12500
/-- The old count numerator/denominator at `kStar` (`countingCoefficient`). -/
def oldNum (p : ℝ) : ℝ := 2*(1-p)*(3*kStar-p)
def oldDen (p : ℝ) : ℝ := 3*kStar*(3-p)-2*p
/-- The old detector count at `kStar` (`countingR kappaStar`). -/
def ROld (δ p : ℝ) : ℝ :=
  1-δ+δ*(oldNum p/oldDen p)*(5/6-δ)/(2*((5/6-δ)+δ*(oldNum p/oldDen p)))

theorem region_box {δ p : ℝ} (h : InRegion δ p) :
    δ ∈ Set.Icc (89/200:ℝ) (97/200) ∧ p ∈ Set.Icc (199/400:ℝ) (1/2) :=
  ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩

theorem regionRow_binding (δ p : ℝ) : regionRowPower δ p =
    JN δ p*(21871/25000-1/1000000-(1+δ)/2-13*(1989/2500)/75+(17287/37500)/2+
      (3137/18750)/2-(3137/18750)*δ*p-(1989/2500)*(1/4-17/50)+
      δ*p*((2*(17287/37500)-(2-Bc)*(1989/2500))/lam)/2)-
    3*(1989/2500)/4*((1-δ)*JN δ p+(5/6-δ)*δ*(1-p)*cN p) := by
  unfold regionRowPower JN DN aN cN lam Bc
  ring

theorem regionCrossLo_binding (δ p : ℝ) : regionCrossLoPower δ p =
    aN p*numT δ p+(2*p*Bc/lam-p)*JN δ p-23/37*DN p*JN δ p := by
  unfold regionCrossLoPower numT JN DN aN cN lam Bc
  ring

theorem regionCrossHi_binding (δ p : ℝ) : regionCrossHiPower δ p =
    DN p*JN δ p-(aN p*numT δ p+(2*p*Bc/lam-p)*JN δ p) := by
  unfold regionCrossHiPower numT JN DN aN cN lam Bc
  ring

theorem regionPlain_binding (δ p : ℝ) : regionPlainPower δ p =
    (1-p)*numT δ p+(p-2*p*Bc/lam)*JN δ p-(mLo+1/100000)*DN p*JN δ p := by
  unfold regionPlainPower numT JN DN aN cN mLo lam Bc
  ring

theorem regionTail_binding (δ p : ℝ) : regionTailPower δ p =
    JN δ p*(-1+2*mHi+2*p*(1-2*mHi)/(6*(3/4)))+(5/6-δ)*(1-p)*cN p := by
  unfold regionTailPower JN DN aN cN mHi lam Bc
  ring

theorem regionCutoff_binding (δ p : ℝ) : regionCutoffPower δ p =
    3/2*JN δ p-numT δ p := by
  unfold regionCutoffPower numT JN DN aN cN lam Bc
  ring

theorem regionCompare_binding (δ p : ℝ) : regionComparePower δ p =
    oldNum p*JN δ p-2*(1-p)*cN p*((5/6-δ)*oldDen p+δ*oldNum p) := by
  unfold regionComparePower oldNum oldDen kStar JN DN aN cN lam Bc
  ring

theorem regionRow_pos {δ p : ℝ} (h : InRegion δ p) : 0 < regionRowPower δ p := by
  obtain ⟨hδ,hp⟩ := region_box h
  rcases le_total δ (93/200) with h1 | h1
  · exact regionRowBox0_pos ⟨hδ.1,h1⟩ hp
  · exact regionRowBox1_pos ⟨h1,hδ.2⟩ hp

theorem region_p {δ p : ℝ} (h : InRegion δ p) : 0 ≤ p ∧ p ≤ 1/2 :=
  ⟨by linarith [h.2.2.1], h.2.2.2⟩

theorem region_DN_pos {δ p : ℝ} (h : InRegion δ p) : 0 < DN p :=
  DN_pos (region_p h).1 (region_p h).2

theorem region_JN_pos {δ p : ℝ} (h : InRegion δ p) : 0 < JN δ p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hV : 0 < 5/6-δ := by linarith
  have hD := DN_pos (p:=p) (by linarith) h4
  have hA := aN_pos (p:=p) (by linarith) h4
  unfold JN
  have : 0 ≤ δ*(1-p)*aN p := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hA.le
  have := mul_pos hV hD
  linarith

theorem region_tN_mul {δ p : ℝ} (h : InRegion δ p) : tN δ p*JN δ p = numT δ p :=
  div_mul_cancel₀ _ (region_JN_pos h).ne'

theorem region_tN {δ p : ℝ} (h : InRegion δ p) : 1 ≤ tN δ p ∧ tN δ p ≤ 3/2 := by
  have hJ := region_JN_pos h
  have hT := region_tN_mul h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc := cN_pos (p:=p) (by linarith) h4
  have hnum : JN δ p ≤ numT δ p := by
    unfold numT JN
    have : 0 ≤ δ*(1-p)*cN p := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hc.le
    nlinarith
  have hcut := regionCutoffBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionCutoff_binding] at hcut
  constructor
  · by_contra hlt
    have := mul_lt_mul_of_pos_right (lt_of_not_ge hlt) hJ
    linarith
  · by_contra hlt
    have := mul_lt_mul_of_pos_right (lt_of_not_ge hlt) hJ
    linarith

theorem region_rN_mul {δ p : ℝ} (h : InRegion δ p) :
    rN p (tN δ p)*DN p = aN p*tN δ p+2*p*Bc/lam-p :=
  div_mul_cancel₀ _ (region_DN_pos h).ne'

theorem region_rN {δ p : ℝ} (h : InRegion δ p) :
    23/37 ≤ rN p (tN δ p) ∧ rN p (tN δ p) ≤ 1 := by
  have hJ := region_JN_pos h
  have hD := region_DN_pos h
  have hT := region_tN_mul h
  have hr := region_rN_mul h
  have hDJ := mul_pos hD hJ
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlo := regionCrossLoBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  have hhi := regionCrossHiBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionCrossLo_binding] at hlo
  rw [regionCrossHi_binding] at hhi
  have klo : (rN p (tN δ p)-23/37)*(DN p*JN δ p) =
      aN p*numT δ p+(2*p*Bc/lam-p)*JN δ p-23/37*DN p*JN δ p := by
    linear_combination (JN δ p)*hr+(aN p)*hT
  have khi : (1-rN p (tN δ p))*(DN p*JN δ p) =
      DN p*JN δ p-(aN p*numT δ p+(2*p*Bc/lam-p)*JN δ p) := by
    linear_combination (-(JN δ p))*hr-(aN p)*hT
  constructor
  · have := (mul_pos_iff_of_pos_right hDJ).mp (klo ▸ hlo)
    linarith
  · have := (mul_pos_iff_of_pos_right hDJ).mp (khi ▸ hhi)
    linarith

theorem region_mN {δ p : ℝ} (h : InRegion δ p) :
    mLo+1/100000 ≤ tN δ p-rN p (tN δ p) := by
  have hJ := region_JN_pos h
  have hD := region_DN_pos h
  have hT := region_tN_mul h
  have hr := region_rN_mul h
  have hDJ := mul_pos hD hJ
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hpl := regionPlainBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionPlain_binding] at hpl
  have k : (tN δ p-rN p (tN δ p)-(mLo+1/100000))*(DN p*JN δ p) =
      (1-p)*numT δ p+(p-2*p*Bc/lam)*JN δ p-(mLo+1/100000)*DN p*JN δ p := by
    have hDa : DN p-aN p = 1-p := by unfold DN aN; ring
    linear_combination (DN p-aN p)*hT-(JN δ p)*hr+(numT δ p)*hDa
  have := (mul_pos_iff_of_pos_right hDJ).mp (k ▸ hpl)
  linarith

theorem region_short {δ p : ℝ} (h : InRegion δ p) :
    shortNew δ p (tN δ p) = RNew δ p :=
  short_at_tN (region_JN_pos h).ne' (region_DN_pos h).ne'

theorem region_max {δ p : ℝ} (h : InRegion δ p) :
    max (shortNew δ p (tN δ p)) (longExp δ (tN δ p)) = RNew δ p :=
  max_at_tN (region_JN_pos h).ne' (region_DN_pos h).ne'

theorem region_RNew_mul {δ p : ℝ} (h : InRegion δ p) :
    (RNew δ p-1+δ)*JN δ p = (5/6-δ)*δ*(1-p)*cN p := by
  unfold RNew
  rw [show 1-δ+(5/6-δ)*δ*(1-p)*cN p/JN δ p-1+δ = (5/6-δ)*δ*(1-p)*cN p/JN δ p by ring]
  exact div_mul_cancel₀ _ (region_JN_pos h).ne'

/-- The old κ-plain tail above `mHi` is dominated by the new short exponent. -/
theorem region_tail {δ p κ : ℝ} (h : InRegion δ p) (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4) :
    oldPlainExp δ p κ mHi ≤ shortNew δ p (tN δ p) := by
  rw [region_short h]
  have hJ := region_JN_pos h
  have hR := region_RNew_mul h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ht := regionTailBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionTail_binding] at ht
  have hk0 : 0 < 6*κ := by linarith
  -- 1/(6κ) ≥ 1/(6*(3/4))
  have hinv : 2*p*(1-2*mHi)/(6*(3/4)) ≤ 2*p*(1-2*mHi)/(6*κ) := by
    apply div_le_div_of_nonneg_left _ hk0 (by linarith)
    unfold mHi; nlinarith
  have hdiff : (RNew δ p-oldPlainExp δ p κ mHi)*JN δ p ≥
      δ*(JN δ p*(-1+2*mHi+2*p*(1-2*mHi)/(6*(3/4)))+(5/6-δ)*(1-p)*cN p) := by
    have e : (RNew δ p-oldPlainExp δ p κ mHi)*JN δ p =
        (RNew δ p-1+δ)*JN δ p+δ*JN δ p*(-1+2*mHi+2*p*(1-2*mHi)/(6*κ)) := by
      unfold oldPlainExp; field_simp; ring
    rw [e, hR]
    have := mul_le_mul_of_nonneg_left hinv (mul_nonneg (by linarith : (0:ℝ) ≤ δ) hJ.le)
    nlinarith
  have hpos : 0 ≤ (RNew δ p-oldPlainExp δ p κ mHi)*JN δ p := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ δ) ht.le
    linarith
  have := nonneg_of_mul_nonneg_left hpos hJ
  linarith

theorem oldDen_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < oldDen p := by
  unfold oldDen kStar; nlinarith

theorem oldNum_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 ≤ oldNum p := by
  unfold oldNum kStar
  apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)

/-- The new count is at most the old count at `kStar` on the region. -/
theorem region_compare {δ p : ℝ} (h : InRegion δ p) : RNew δ p ≤ ROld δ p := by
  have hJ := region_JN_pos h
  have hR := region_RNew_mul h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc := regionCompareBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionCompare_binding] at hc
  have hD := oldDen_pos (p:=p) (by linarith) h4
  have hN := oldNum_nonneg (p:=p) (by linarith) h4
  have hcN := cN_pos (p:=p) (by linarith) h4
  set c := oldNum p/oldDen p with hcdef
  have hc0 : 0 ≤ c := div_nonneg hN hD.le
  have hcD : c*oldDen p = oldNum p := div_mul_cancel₀ _ hD.ne'
  have hV : 0 < 5/6-δ := by linarith
  have hS : 0 < (5/6-δ)+δ*c := by nlinarith
  -- RNew - (1-δ) = Vδ(1-p)cN/JN ≤ δ c V/(2 S)
  have hlhs : RNew δ p-(1-δ) = (5/6-δ)*δ*(1-p)*cN p/JN δ p := by unfold RNew; ring
  have hrhs : ROld δ p-(1-δ) = δ*c*(5/6-δ)/(2*((5/6-δ)+δ*c)) := by unfold ROld; ring
  have key : (5/6-δ)*δ*(1-p)*cN p/JN δ p ≤ δ*c*(5/6-δ)/(2*((5/6-δ)+δ*c)) := by
    rw [div_le_div_iff₀ hJ (by positivity)]
    -- cross-multiplied: Vδ(1-p)cN * 2S ≤ δ c V JN; divide by Vδ ≥ 0 and use certificate
    have hcert : 2*(1-p)*cN p*((5/6-δ)+δ*c) ≤ c*JN δ p := by
      have e1 : (c*JN δ p-2*(1-p)*cN p*((5/6-δ)+δ*c))*oldDen p =
          oldNum p*JN δ p-2*(1-p)*cN p*((5/6-δ)*oldDen p+δ*oldNum p) := by
        linear_combination (JN δ p-2*(1-p)*cN p*δ)*hcD
      have := (mul_pos_iff_of_pos_right hD).mp (e1 ▸ hc)
      linarith
    have hVδ : 0 ≤ (5/6-δ)*δ := mul_nonneg hV.le (by linarith)
    have := mul_le_mul_of_nonneg_left hcert hVδ
    nlinarith
  linarith

end
end DetectorAffine
