/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The exact tangent's admitted count window. Adapted from Sil's PR137 window
(copyright (c) 2026 Sil, Apache-2.0), retaining Collet's native contracts.
The exact line uses a uniform enclosure certificate, not rounded coefficients. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactWindowGuards
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ExactWindow
noncomputable section
open Set QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning
open QRH.Record1252270103Return (plainCurve)
open Qrh.MarkedAnchor.Interface (anchorLeft anchorTop)
open Qrh.TwoSlot.AnchorContinuum.Contact
def kI (p : ℝ) : ℝ := 1-p*(1+2*exactLine.g1)
def aI (p : ℝ) : ℝ := p*(1+2*exactLine.g0)
def UI (p : ℝ) : ℝ := 1-p*(1+6*exactLine.g0-4*exactLine.g1)
def JI (δ p : ℝ) : ℝ := 3*(5/6-δ)+2*δ*kI p
def NI (δ p : ℝ) : ℝ := (1-δ)*JI δ p+(5/6-δ)*δ*UI p
def TI (δ p : ℝ) : ℝ := JI δ p+δ*UI p
def valueI (δ p : ℝ) : ℝ := NI δ p/JI δ p
def cutoffI (δ p : ℝ) : ℝ := TI δ p/JI δ p
def crossingI (δ p : ℝ) : ℝ := 2*TI δ p/(3*JI δ p)
def dUI : ℝ := -(1+6*exactLine.g0-4*exactLine.g1)
def dJI (δ : ℝ) : ℝ := -2*δ*(1+2*exactLine.g1)


section
variable {δ p : ℝ} (hδ : δ ∈ Icc (189/512:ℝ) (15/32)) (hp : p ∈ Icc (15/32:ℝ) (1/2))
include hδ hp

theorem hk : 0 < kI p := by
  exact WindowGuards.exact_guards 0 hδ hp

theorem hJ : 0 < JI δ p := by
  exact WindowGuards.exact_guards 1 hδ hp

theorem hT1 : JI δ p < TI δ p := by
  have hh := WindowGuards.exact_guards 2 hδ hp
  change 0 < TI δ p-JI δ p at hh
  linarith

theorem hT2 : TI δ p < 12499/10000*JI δ p := by
  have hh := WindowGuards.exact_guards 3 hδ hp
  change 0 < 12499/10000*JI δ p-TI δ p at hh
  linarith

theorem hcross : (anchorLeft+1/1000000)*(3*JI δ p) < 2*TI δ p := by
  have hh := WindowGuards.exact_guards 4 hδ hp
  change 0 < 2*TI δ p-3*(anchorLeft+1/1000000)*JI δ p at hh
  nlinarith only [hh]

theorem hnat : (1-δ*(p+(1-p)*anchorTop))*JI δ p < NI δ p := by
  have hh := WindowGuards.exact_guards 5 hδ hp
  change 0 < NI δ p-(1-δ*(anchorTop+(1-anchorTop)*p))*JI δ p at hh
  nlinarith only [hh]

theorem hplain1 : (1-δ*(anchorTop+2*(countCB-anchorTop)/countCL*p))*JI δ p < NI δ p := by
  have hh := WindowGuards.exact_guards 6 hδ hp
  change 0 < NI δ p-(1-δ*(anchorTop+(2*(countCB-anchorTop)/countCL)*p))*JI δ p at hh
  linarith

theorem hplain0 : (1-δ*(anchorTop+2*(countCap-1/10000000)*p))*JI δ p < NI δ p := by
  have hh := WindowGuards.exact_guards 7 hδ hp
  change 0 < NI δ p-(1-δ*(anchorTop+2*(countCap-1/10000000)*p))*JI δ p at hh
  linarith

theorem htail : (1-2*δ*naturalM-2*δ*p*sMinus)*JI δ p < NI δ p := by
  have hh := WindowGuards.exact_guards 8 hδ hp
  change 0 < NI δ p-(1-2*naturalM*δ-2*sMinus*δ*p)*JI δ p at hh
  nlinarith only [hh]

theorem hanti : 0 < UI p*dJI δ-dUI*JI δ p := by
  have hh := WindowGuards.exact_guards 9 hδ hp
  change 0 < UI p*(-2*(1+2*exactLine.g1)*δ)+(1+6*exactLine.g0-4*exactLine.g1)*JI δ p at hh
  unfold dJI dUI
  nlinarith only [hh]

end
theorem crossing_eq (δ p : ℝ) (hJ : JI δ p≠0) :
    2*(cutoffI δ p-crossingI δ p)=crossingI δ p := by
  unfold cutoffI crossingI; field_simp; ring

theorem inverse_identity (δ p : ℝ) (hJ : JI δ p≠0) :
    1-δ*(p*(1+2*exactLine.g0)+(1-p*(1+2*exactLine.g1))*crossingI δ p)=valueI δ p := by
  unfold crossingI valueI; field_simp; unfold NI TI JI UI kI; ring

theorem long_identity (δ p : ℝ) (hJ : JI δ p≠0) :
    1-δ+(5/6-δ)*(cutoffI δ p-1)=valueI δ p := by
  unfold cutoffI valueI; field_simp; unfold NI TI; ring

theorem UI_hasDerivAt (p : ℝ) : HasDerivAt UI dUI p := by
  have h := ((hasDerivAt_id p).mul_const (1+6*exactLine.g0-4*exactLine.g1)).const_sub 1
  convert h using 1
  · funext z; simp only [UI,id]
  · unfold dUI; ring

theorem JI_hasDerivAt (δ p : ℝ) : HasDerivAt (JI δ) (dJI δ) p := by
  have h := ((((hasDerivAt_id p).mul_const (1+2*exactLine.g1)).const_sub 1).const_mul (2*δ)).const_add
    (3*(5/6-δ))
  convert h using 1
  · funext z; simp only [JI,kI,id]
  · unfold dJI; ring

theorem valueI_ratio {δ p : ℝ} (hj : JI δ p≠0) :
    valueI δ p=1-δ+(5/6-δ)*δ*(UI p/JI δ p) := by
  unfold valueI NI; field_simp; try ring

theorem valueI_hasDerivAt {δ p : ℝ} (hj : JI δ p≠0) :
    HasDerivAt (valueI δ) ((5/6-δ)*δ*(-(UI p*dJI δ-dUI*JI δ p))/(JI δ p)^2) p := by
  have hq := (UI_hasDerivAt p).div (JI_hasDerivAt δ p) hj
  have hn := (JI_hasDerivAt δ p).continuousAt.eventually_ne hj
  have he : valueI δ =ᶠ[nhds p] (fun z=>1-δ+(5/6-δ)*δ*(UI z/JI δ z)) :=
    hn.mono (fun z hz=>valueI_ratio hz)
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert (hasDerivAt_const p (1-δ)).add (hq.const_mul ((5/6-δ)*δ)) using 1 <;> (try funext z) <;> ring

theorem valueI_antitoneOn {δ : ℝ} (hδ : δ∈Icc (189/512:ℝ) (15/32)) :
    AntitoneOn (valueI δ) (Icc (15/32:ℝ) (1/2)) := by
  have hj (p : ℝ) (hp : p∈Icc (15/32:ℝ) (1/2)) : 0<JI δ p := hJ hδ hp
  have hh (p : ℝ) (hp : p∈Icc (15/32:ℝ) (1/2)) := valueI_hasDerivAt (hj p hp).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro p hp; exact (hh p hp).continuousAt.continuousWithinAt
  · intro p hp; exact (hh p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hh p (interior_subset hp)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith [hδ.2]) (by linarith [hδ.1]))
        (neg_nonpos.mpr (hanti hδ (interior_subset hp)).le)
    · exact sq_nonneg _

/-- **The improved window** `[189/512, 15/32] × [15/32, 1/2]` (line `(exactLine.g0, exactLine.g1)`, native
plain fallback on the count face `C`). -/
def window : ImprovedWindow exactLine (naturalK/6) where
  B := countCB
  lam := countCL
  cap := countCap-1/10000000
  sourceCap := countCap
  mHi := naturalM
  lam_gt_one := by norm_num [countCL]
  mHi_lo := natural_join_bounds.1
  mHi_hi := natural_join_bounds.2
  cap_le_source := by linarith
  cap_small := by norm_num [countCap]
  value := valueI
  cutoff := cutoffI
  crossing := crossingI
  deltaLo := 189/512
  deltaHi := 15/32
  pLo := 15/32
  deltaBounds := by norm_num
  pBounds := by norm_num
  cutoff_bounds := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    exact ⟨(le_div_iff₀ hJ').mpr (by linarith [hT1 hd hp]),
      (div_le_iff₀ hJ').mpr (by linarith [hT2 hd hp])⟩
  crossing_left := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    unfold crossingI
    rw [le_div_iff₀ (by linarith)]
    have := hcross hd hp
    unfold anchorLeft at this ⊢
    linarith
  plain_left := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    rw [crossing_eq δ p hJ'.ne']
    unfold crossingI
    rw [le_div_iff₀ (by linarith)]
    have := hcross hd hp
    linarith
  slope_nonneg := by intro δ p hd hp; exact (hk hd hp).le
  inverse_crossing := by intro δ p hd hp; exact inverse_identity δ p (hJ hd hp).ne'
  ordinary_crossing := by
    intro δ p hd hp
    rw [crossing_eq δ p (hJ hd hp).ne']
    have e := inverse_identity δ p (hJ hd hp).ne'
    apply le_of_eq
    rw [← e]; ring
  native_top := by
    intro δ p hd hp
    unfold valueI
    rw [le_div_iff₀ (hJ hd hp)]
    linarith [hnat hd hp]
  plain_top := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    unfold valueI plainCurve
    apply max_le
    · rw [le_div_iff₀ hJ']
      have h := hplain0 hd hp
      linarith
    · rw [le_div_iff₀ hJ']
      have h := hplain1 hd hp
      have e : (1-2*δ*(anchorTop/2)-2*δ*p*(countCB-2*(anchorTop/2))/countCL)*JI δ p=
          (1-δ*(anchorTop+2*(countCB-anchorTop)/countCL*p))*JI δ p := by ring
      rw [e]; exact h.le
  natural_tail := by
    intro δ p hd hp
    have he : (1-2*naturalM)/(6*(naturalK/6))=sMinus := by norm_num [naturalM,naturalK,sMinus]
    rw [mul_div_assoc,he]
    unfold valueI
    rw [le_div_iff₀ (hJ hd hp)]
    have := htail hd hp
    linarith
  widths := by
    intro ν hν m hm1 hm2
    have hM : naturalM=(1-naturalK*sMinus)/2 := rfl
    apply lt_min
    · unfold countCap; linarith
    · rw [hM] at hm2
      norm_num [naturalK,sMinus] at hm2
      rw [lt_div_iff₀ (by norm_num [countCL])]
      norm_num [countCB,countCL]
      linarith
  long_crossing := by intro δ p hd hp; exact long_identity δ p (hJ hd hp).ne'
  antitone := by intro δ hd; exact valueI_antitoneOn hd

end
end Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ExactWindow
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ExactWindow.window
