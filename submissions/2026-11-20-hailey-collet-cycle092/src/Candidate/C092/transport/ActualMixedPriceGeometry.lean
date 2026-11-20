/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.ActualMixedPrice

/-! The endpoint parameters in Q2 really enclose the live k and crossing t₀/3.
These are scalar geometric facts, separate from the analytic count contract. -/
set_option autoImplicit false
namespace QRH.Cycle092.ActualMixedPrice
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
open QRH.ContactCertificate QRH.Coverage
noncomputable section

theorem receipt_corner_bounds :
    (0 : ℝ)≤(g0Receipt.lo : ℝ) ∧ (g0Receipt.lo : ℝ)≤3/50 ∧
    (7/100 : ℝ)≤(g1Receipt.lo : ℝ) ∧ (g1Receipt.lo : ℝ)≤(g1Receipt.hi : ℝ) ∧
    (g1Receipt.hi : ℝ)≤2/25 ∧
    1≤1+6*(g0Receipt.lo : ℝ)-4*(g1Receipt.hi : ℝ) := by
  norm_num [g0Receipt,g1Receipt]

theorem actual_k_bounds {r : Row} (hr : r∈rows) {point : Point}
    (hp : r.box.Contains point) {x : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval x) :
    (rowKLower r.box : ℝ)≤pairedK point.2 (g1 (wValue x)) ∧
    pairedK point.2 (g1 (wValue x))≤(rowKUpper r.box : ℝ) := by
  have hs := Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have hg := Top.point_guards hs hp
  have hc := g1_receipt_sound hx
  have hrec := receipt_corner_bounds
  have hhi : 0≤(r.box.vHi : ℝ) := hg.2.2.1.trans hp.2.2.2
  have hlo : 0≤(r.box.vLo : ℝ) := Rat.cast_nonneg.mpr hs.2.2.2.2.1
  have hc₀ : 0≤1+2*(g1Receipt.lo : ℝ) := by linarith [hrec.2.2.1]
  have hc₁ : 0≤1+2*g1 (wValue x) := by linarith [hrec.2.2.1,hc.1]
  have h₀ := mul_le_mul hp.2.2.2 (by linarith [hc.2] :
    1+2*g1 (wValue x)≤1+2*(g1Receipt.hi : ℝ)) hc₁ hhi
  have h₁ := mul_le_mul hp.2.2.1 (by linarith [hc.1] :
    1+2*(g1Receipt.lo : ℝ)≤1+2*g1 (wValue x)) hc₀ hg.2.2.1
  dsimp [pairedK,rowKLower,rowKUpper]
  simp only [Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat]
  constructor <;> linarith

/-- Crossing monotonicity in d follows from one exact denominator identity. -/
theorem crossing_monotone_d {d b p g₀ g₁ : ℝ} (hdb : d≤b)
    (hU : 0≤pairedU p g₀ g₁)
    (hJd : 0<pairedJ d p g₁) (hJb : 0<pairedJ b p g₁) :
    pairedCrossing d p g₀ g₁≤pairedCrossing b p g₀ g₁ := by
  have hid : b*pairedU p g₀ g₁*pairedJ d p g₁-
      d*pairedU p g₀ g₁*pairedJ b p g₁ = (5/2)*pairedU p g₀ g₁*(b-d) := by
    dsimp [pairedJ,pairedV,pairedK]
    ring
  have hn : 0≤(5/2 : ℝ)*pairedU p g₀ g₁*(b-d) :=
    mul_nonneg (mul_nonneg (by norm_num) hU) (sub_nonneg.mpr hdb)
  have hq : d*pairedU p g₀ g₁/pairedJ d p g₁≤
      b*pairedU p g₀ g₁/pairedJ b p g₁ :=
    (div_le_div_iff₀ hJd hJb).mpr (by linarith [hid])
  dsimp [pairedCrossing]
  linarith [hq]

/-- Crossing is antitone in p when the exact derivative numerator is positive;
the proof is a finite difference, so closed boundaries need no derivatives. -/
theorem crossing_antitone_p {d a p g₀ g₁ : ℝ} (hap : a≤p) (hd : 0≤d)
    (hC : 0≤(5/2-d)*(1+6*g₀-4*g₁)-2*d*(1+2*g₁))
    (hJa : 0<pairedJ d a g₁) (hJp : 0<pairedJ d p g₁) :
    pairedCrossing d p g₀ g₁≤pairedCrossing d a g₀ g₁ := by
  have hid : d*pairedU a g₀ g₁*pairedJ d p g₁-
      d*pairedU p g₀ g₁*pairedJ d a g₁ =
      d*(p-a)*((5/2-d)*(1+6*g₀-4*g₁)-2*d*(1+2*g₁)) := by
    dsimp [pairedU,pairedJ,pairedV,pairedK]
    ring
  have hn := mul_nonneg (mul_nonneg hd (sub_nonneg.mpr hap)) hC
  have hq : d*pairedU p g₀ g₁/pairedJ d p g₁≤
      d*pairedU a g₀ g₁/pairedJ d a g₁ :=
    (div_le_div_iff₀ hJp hJa).mpr (by linarith [hid])
  dsimp [pairedCrossing]
  linarith [hq]

theorem crossing_contact_upper {d p x : ℝ}
    (hd : 0≤d) (hd' : d≤1/2) (hp : 0≤p) (hp' : p≤1/2)
    (hx : QRH.RationalInterval.Contains alphaInterval x) :
    pairedCrossing d p (g0 (wValue x)) (g1 (wValue x))≤
      pairedCrossing d p (g0Receipt.lo : ℝ) (g1Receipt.hi : ℝ) := by
  have hc := Physical.actual_contact_bounds hx
  have h₀ := g0_receipt_sound hx
  have h₁ := g1_receipt_sound hx
  have hr := receipt_corner_bounds
  have hag₀ : 0≤g0 (wValue x) := hr.1.trans h₀.1
  have hag₀' : g0 (wValue x)≤3/50 := by linarith [hc.2.1]
  have hag₁ : 7/100≤g1 (wValue x) := hr.2.2.1.trans h₁.1
  have hag₁' : g1 (wValue x)≤2/25 := h₁.2.trans hr.2.2.2.2.1
  have ha := Physical.admitted hd hd' hp hp' hag₀ hag₀' hag₁ hag₁'
  have hb := Physical.admitted hd hd' hp hp' hr.1 hr.2.1 hag₁ hag₁'
  have he := Physical.admitted hd hd' hp hp' hr.1 hr.2.1
    (hr.2.2.1.trans hr.2.2.2.1) hr.2.2.2.2.1
  have hcount := (pairedCount_antitone_g₀ hd (by linarith) hp h₀.1 ha.2.1).trans
    (pairedCount_monotone_g₁ hd (by linarith) hp h₁.2 hb.1 hb.2.1 he.2.1)
  rw [pairedCount_eq ha.2.1.ne',pairedCount_eq he.2.1.ne'] at hcount
  have hv : 0<pairedV d := by dsimp [pairedV]; linarith
  nlinarith

/-- The exact rational m used by the all-row bank bounds the true pointwise
crossing at the authentic algebraic contact throughout every mixed box. -/
theorem actual_crossing_upper {r : Row} (hr : r∈rows) {point : Point}
    (hp : r.box.Contains point) {x : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval x) :
    pairedCrossing point.1 point.2 (g0 (wValue x)) (g1 (wValue x))/3≤
      (rowM r.box : ℝ) := by
  have hs := Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have hg := Top.point_guards hs hp
  have hd : 0≤(r.box.uHi : ℝ) := hg.1.trans hp.2.1
  have hd' : (r.box.uHi : ℝ)≤(1/2 : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      ((Rat.cast_le (K:=ℝ)).mpr hs.2.2.2.1)
  have ha : 0≤(r.box.vLo : ℝ) := Rat.cast_nonneg.mpr hs.2.2.2.2.1
  have ha' : (r.box.vLo : ℝ)≤1/2 := hp.2.2.1.trans hg.2.2.2
  have hrb := receipt_corner_bounds
  have hadm (d p : ℝ) (hd : 0≤d) (hd' : d≤1/2) (hp : 0≤p) (hp' : p≤1/2) :=
    Physical.admitted hd hd' hp hp' hrb.1 hrb.2.1
      (hrb.2.2.1.trans hrb.2.2.2.1) hrb.2.2.2.2.1
  have h₀ := crossing_contact_upper hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 hx
  have h₁ := crossing_monotone_d hp.2.1 (hadm _ _ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).1
    (hadm _ _ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).2.1
    (hadm _ _ hd hd' hg.2.2.1 hg.2.2.2).2.1
  have hC : 0≤(5/2-(r.box.uHi : ℝ))*
      (1+6*(g0Receipt.lo : ℝ)-4*(g1Receipt.hi : ℝ))-
      2*(r.box.uHi : ℝ)*(1+2*(g1Receipt.hi : ℝ)) := by
    have hA := mul_nonneg (sub_nonneg.mpr hrb.2.2.2.2.2)
      (show 0≤5/2-(r.box.uHi : ℝ) by linarith)
    have hB : 0≤1+2*(g1Receipt.hi : ℝ) := by linarith [hrb.2.2.1,hrb.2.2.2.1]
    have hB' := mul_le_mul_of_nonneg_right (show 2*(r.box.uHi : ℝ)≤1 by linarith) hB
    nlinarith [hrb.2.2.2.2.1]
  have h₂ := crossing_antitone_p hp.2.2.1 hd hC
    (hadm _ _ hd hd' ha ha').2.1 (hadm _ _ hd hd' hg.2.2.1 hg.2.2.2).2.1
  rw [rowM_cast]
  linarith [h₀.trans (h₁.trans h₂)]

end
end QRH.Cycle092.ActualMixedPrice
#print axioms QRH.Cycle092.ActualMixedPrice.actual_k_bounds
#print axioms QRH.Cycle092.ActualMixedPrice.actual_crossing_upper
