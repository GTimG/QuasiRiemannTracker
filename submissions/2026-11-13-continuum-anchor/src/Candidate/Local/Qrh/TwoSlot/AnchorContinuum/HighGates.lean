/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.Tolerances
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Algebra
import Mathlib.Tactic.LinearCombination

/-! The HIGH class ledger at a variable coupled tolerance. The structural
inequalities use the existing stage algebra; the short and long prices retain
the chosen source pad and witness shift explicitly. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorContinuum.HighGates
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss.High
open Tolerances

def cutoff (d : Stg) (q ν : ℝ) : ℝ := d.g ν/d.H+q

theorem cutoff_above {d : Stg} {q fee ν : ℝ} (h : d.Hyp fee) (hν : d.k ≤ ν) :
    d.R+q ≤ cutoff d q ν := by
  have hg := Stg.g_ge_r h hν
  have hR : d.R ≤ d.g ν/d.H := by
    rw [le_div_iff₀ h.H_pos]
    simpa only [Stg.r, mul_comm] using hg
  unfold cutoff
  linarith

theorem cutoff_mem {d : Stg} {q fee ν : ℝ} (h : d.Hyp fee)
    (hq : 0 ≤ q) (hqu : q ≤ 1/1000000000000) (hR : 3/4 ≤ d.R)
    (hν : d.k ≤ ν) (hν1 : ν ≤ 3/4) : cutoff d q ν ∈ cutoffs := by
  have ha := cutoff_above (q:=q) h hν
  have hw := Stg.w_mem h hν hν1
  constructor
  · unfold cutLo
    linarith
  · have hle : cutoff d q ν ≤ d.w ν := by unfold cutoff Stg.w; linarith
    exact hle.trans hw.2

theorem supply {d : Stg} {q fee ν : ℝ} (h : d.Hyp fee)
    (hq : 0 ≤ q) (hν : d.k ≤ ν) :
    d.H * Tolerances.sig q d.a0 d.a1 (cutoff d q ν) ≤ d.s := by
  have hw := cutoff_above (q:=q) h hν
  have hs := h.s_nonneg
  unfold Tolerances.sig
  rcases le_total 0 ((1-cutoff d q ν)/2+(d.a0-d.a1*cutoff d q ν)-sourcePad q) with hx | hx
  · rw [max_eq_right hx]
    have hprod := mul_le_mul_of_nonneg_left (show d.R ≤ cutoff d q ν by linarith)
      h.a1_nonneg
    have hp : 0 ≤ sourcePad q := div_nonneg hq (by norm_num)
    have hline : (1-cutoff d q ν)/2+(d.a0-d.a1*cutoff d q ν)-sourcePad q ≤
        (1-d.R)/2+d.z := by linarith [h.line]
    have hbase : d.H*((1-d.R)/2+d.z) ≤ d.s := by
      unfold Stg.s
      have := div_nonneg h.u_nonneg h.k_pos.le
      linarith
    exact (mul_le_mul_of_nonneg_left hline h.H_pos.le).trans hbase
  · rw [max_eq_left hx, mul_zero]
    exact hs

theorem short_le {d : Stg} {q fee ν e : ℝ} (h : d.Hyp fee) (hq : 0 ≤ q)
    (hν : d.k ≤ ν) (he0 : 0 ≤ e) (he : e ≤ ν) :
    ν*d.r+e*d.s+Tolerances.shortCnt q d.a0 d.a1 ν e (cutoff d q ν) d.s d.H-d.H ≤ d.u := by
  have hH := h.H_pos
  have ha1 := h.a1_nonneg
  have hν0 : 0 < ν := h.k_pos.trans_le hν
  have hb := Stg.excess_B3 h hν he0 he
  let X := (1-cutoff d q ν)/2+(d.a0-d.a1*cutoff d q ν)-sourcePad q
  have hm : d.H*X ≤ min d.s (d.H*Tolerances.sig q d.a0 d.a1 (cutoff d q ν)) := by
    have hx : X ≤ Tolerances.sig q d.a0 d.a1 (cutoff d q ν) := le_max_right _ _
    have hh := mul_le_mul_of_nonneg_left hx h.H_pos.le
    exact le_min (hh.trans (supply h hq hν)) hh
  have hemin := mul_le_mul_of_nonneg_left hm he0
  have hw : d.H*cutoff d q ν = d.g ν+d.H*q := by
    unfold cutoff
    field_simp
  have hX : d.H*X = (d.H-d.g ν)/2+(d.H*d.a0-d.a1*d.g ν)-
      d.H*((1/2+d.a1)*q+q/10) := by
    dsimp [X, sourcePad]
    linear_combination (-(1/2:ℝ)-d.a1)*hw
  have hc0 : 0 ≤ (1/2+d.a1)*q+q/10 := by positivity
  have hc1 : (1/2+d.a1)*q+q/10 ≤ q := by
    nlinarith [mul_le_mul_of_nonneg_right h.a1_le hq]
  have hp1 := mul_le_mul_of_nonneg_left hc1 h.H_pos.le
  have hp2 := mul_le_mul_of_nonneg_right he (mul_nonneg h.H_pos.le hc0)
  have hp3 := mul_le_mul_of_nonneg_left hp1 hν0.le
  have hpad : e*(d.H*((1/2+d.a1)*q+q/10)) ≤ ν*(d.H*q) := hp2.trans hp3
  unfold Tolerances.shortCnt
  have hn : ν*d.H*cutoff d q ν = ν*(d.g ν+d.H*q) := by rw [mul_assoc, hw]
  rw [hn]
  rw [hX] at hemin
  nlinarith

theorem long_le {d : Stg} {q ν e : ℝ} (h : d.Hyp (30*q)) (hq : 0 < q)
    (hν : d.k ≤ ν) (hν1 : ν ≤ 3/4) (he : e ≤ ν) :
    ν*d.r+e*d.s+Tolerances.longCnt q ν (cutoff d q ν) d.H-d.H ≤ d.u := by
  have hH := h.H_pos
  have hν0 : 0 < ν := h.k_pos.trans_le hν
  have hgk := Stg.G_k h
  have hgm := Stg.G_mono h hν hν1
  have hF := h.gF0
  have hes := mul_le_mul_of_nonneg_right he h.s_nonneg
  have hw : d.H*cutoff d q ν = d.g ν+d.H*q := by unfold cutoff; field_simp
  have hl : Tolerances.longCnt q ν (cutoff d q ν) d.H =
      d.H/6+(5/6-ν)*(3*d.g ν/2)+(5/6-ν)*d.H*(5*q/2) := by
    unfold Tolerances.longCnt
    linear_combination (3/2*(5/6-ν))*hw
  have hp : (5/6-ν)*d.H*(5*q/2) ≤ 5*q/2 := by
    have hc : (5/6-ν)*d.H ≤ 1 := by nlinarith [h.H_le, mul_nonneg hν0.le h.H_pos.le]
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (one_mul _)
  rw [hl]
  have hg : d.G ν = d.H+d.u-d.H/6-(5/6-ν)*(3*d.g ν/2)-ν*(d.r+d.s) := rfl
  nlinarith

/-- The exact class hypotheses consumed by the variable-tolerance paired step. -/
theorem class_gates {d : Stg} {q : ℝ} (h : d.Hyp (30*q))
    (hq : 0 < q) (hqu : q ≤ 1/1000000000000) (hR : 3/4 ≤ d.R)
    (ha0 : d.a0 ≤ 1) :
    ∀ p ∈ classes d.k, ∃ w ∈ cutoffs, d.R+q ≤ w ∧
      w+Tolerances.sig q d.a0 d.a1 w ≤ 6 ∧
      Tolerances.detEx q d.a0 d.a1 p.1 p.2 w d.r d.s d.H ≤ d.u := by
  intro p hp
  obtain ⟨hν,hν1,he0,he⟩ := hp
  have hw := cutoff_mem h hq.le hqu hR hν hν1
  refine ⟨cutoff d q p.1,hw,cutoff_above h hν,?_,?_⟩
  · have hwp : 0 ≤ cutoff d q p.1 := by have := hw.1; unfold cutLo at this; linarith
    have ha := mul_nonneg h.a1_nonneg hwp
    have hs : Tolerances.sig q d.a0 d.a1 (cutoff d q p.1) ≤ 3/2 := by
      unfold Tolerances.sig sourcePad
      apply max_le (by norm_num)
      linarith
    have hwh := hw.2
    unfold cutHi at hwh
    linarith
  · have hs := short_le h hq.le hν he0 he
    have hl := long_le h hq hν hν1 he
    unfold Tolerances.detEx
    rcases le_total (Tolerances.shortCnt q d.a0 d.a1 p.1 p.2 (cutoff d q p.1) d.s d.H)
      (Tolerances.longCnt q p.1 (cutoff d q p.1) d.H) with hc | hc
    · rw [max_eq_right hc]
      exact hl
    · rw [max_eq_left hc]
      exact hs

end
end Qrh.TwoSlot.AnchorContinuum.HighGates
