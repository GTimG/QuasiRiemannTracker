/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
A finite common source grid from preceding anchors. The grid size is abstract;
no numerical stage list or number of stages occurs in this theorem. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.Sources

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss.High.Marked
noncomputable section
open scoped Classical
open Qrh.MarkedAnchor.Interface.Contract Qrh.TwoSlot.AnchorZeroLoss.High

/-- A uniform strict minorant of preceding anchors supplies finitely many
paired source rectangles covering the entire required HIGH interval. -/
theorem finite_grid_of_earlier_with_pad (R T wlo a0 a1 gap topGap step pad : ℝ)
    (hR : R<wlo) (hwlo : 0≤wlo) (hT : T≤7/9) (ha1 : 0≤a1) (ha1hi : a1≤2/5)
    (htop : 0<topGap) (hh : 0<step) (hhhi : step≤1/1000)
    (hstep : 2*step≤topGap)
    (hbudget : step+2*(1/2+a1)*step≤gap+pad)
    (hprior : ∀ r : ℝ,R<r → r≤T → ∃z : ℝ,0≤z ∧
      a0-a1*r+gap≤z ∧ AnchorAt r z) :
    ∃ (N : ℕ) (ρ : Fin N → AnchorRect),
      (∀k,UniformInverseRectSource canonicalFamily (ρ k) ∧ OrdinaryRectSource (ρ k)) ∧
      ∀ x : ℝ,wlo≤x → x<T-topGap → ∃k,(ρ k).Admissible x (max 0 ((1-x)/2+(a0-a1*x)-pad)) 1 := by
  by_cases hwt : wlo<T
  · let N : ℕ := ⌈(T-wlo)/step⌉₊+1
    let rp : Fin N → ℝ := fun k=>min (wlo+(k.val:ℝ)*step+2*step) T
    have hrp (k : Fin N) : R<rp k ∧ rp k≤T := by
      have hk : (0:ℝ)≤k.val := Nat.cast_nonneg _
      refine ⟨lt_min ?_ (hR.trans hwt),min_le_right _ _⟩
      nlinarith
    choose gain hgain0 hgain hanchor using fun k=>hprior (rp k) (hrp k).1 (hrp k).2
    let ρ : Fin N → AnchorRect := fun k=>anchorRect (rp k) (gain k) step
    refine ⟨N,ρ,fun k=>hanchor k step hh,?_⟩
    intro x hxlo hxhi
    have hxR : R<x := hR.trans_le hxlo
    have hx0 : 0≤x := hwlo.trans hxlo
    let q : ℕ := ⌊(x-wlo)/step⌋₊
    have hq0 : 0≤(x-wlo)/step := div_nonneg (by linarith) hh.le
    have hq1 : (q:ℝ)≤(x-wlo)/step := Nat.floor_le hq0
    have hq2 : (x-wlo)/step<(q:ℝ)+1 := Nat.lt_floor_add_one _
    have heq : (x-wlo)/step*step=x-wlo := div_mul_cancel₀ _ hh.ne'
    have hlow := mul_le_mul_of_nonneg_right hq1 hh.le
    have hhigh := mul_lt_mul_of_pos_right hq2 hh
    have hqN : q<N := by
      have hb : (x-wlo)/step≤(T-wlo)/step :=
        div_le_div_of_nonneg_right (by linarith) hh.le
      have hc : (T-wlo)/step≤(⌈(T-wlo)/step⌉₊:ℝ) := Nat.le_ceil _
      have hn : (q:ℝ)<(N:ℝ) := by dsimp [N]; push_cast; linarith
      exact_mod_cast hn
    let k : Fin N := ⟨q,hqN⟩
    have hrpk : rp k=wlo+(q:ℝ)*step+2*step := by
      dsimp [rp,k]
      apply min_eq_left
      linarith
    have hdelta : 0≤rp k-x ∧ rp k-x≤2*step := by rw [hrpk]; constructor <;> linarith
    refine ⟨k,hx0,?_,le_max_left _ _,?_⟩
    · change x≤(rp k-step)*1
      rw [hrpk]
      linarith
    · change max 0 ((1-x)/2+(a0-a1*x)-pad)≤((1-rp k)/2+gain k-step)*1
      rw [mul_one]
      apply max_le
      · have := (hrp k).2
        have := hgain0 k
        linarith
      · have hp := mul_le_mul_of_nonneg_left hdelta.2
          (show 0≤1/2+a1 by linarith)
        have hz := hgain k
        nlinarith
  · refine ⟨0,Fin.elim0,fun k=>k.elim0,?_⟩
    intro x hxlo hxhi
    have : T≤wlo := le_of_not_gt hwt
    linarith


/-- Compatibility with the frozen finite source tolerance. -/
theorem finite_grid_of_earlier (R T wlo a0 a1 gap topGap step : ℝ)
    (hR : R<wlo) (hwlo : 0≤wlo) (hT : T≤7/9) (ha1 : 0≤a1) (ha1hi : a1≤2/5)
    (htop : 0<topGap) (hh : 0<step) (hhhi : step≤1/1000)
    (hstep : 2*step≤topGap)
    (hbudget : step+2*(1/2+a1)*step≤gap+1/10000000000000)
    (hprior : ∀ r : ℝ,R<r → r≤T → ∃z : ℝ,0≤z ∧
      a0-a1*r+gap≤z ∧ AnchorAt r z) :
    ∃ (N : ℕ) (ρ : Fin N → AnchorRect),
      (∀k,UniformInverseRectSource canonicalFamily (ρ k) ∧ OrdinaryRectSource (ρ k)) ∧
      ∀ x : ℝ,wlo≤x → x<T-topGap → ∃k,(ρ k).Admissible x (sig a0 a1 x) 1 := by
  simpa only [sig] using finite_grid_of_earlier_with_pad R T wlo a0 a1 gap topGap step
    (1/10000000000000) hR hwlo hT ha1 ha1hi htop hh hhhi hstep hbudget hprior

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Marked
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Marked.finite_grid_of_earlier
