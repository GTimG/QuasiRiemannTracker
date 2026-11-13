/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CurveStep
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.NativeSeed

/-! Finite induction supplies the entire strict curve. Every use of the
analytic stage theorem has only already established anchors as inputs. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Set Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native

theorem strict_curve_anchor (F : ParentFace)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    {lam T : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hT : 3/4 ≤ T) (hT1 : T < 7/9) :
    ∀ r ∈ Icc (3/4:ℝ) T, AnchorAt r (Curve.W lam T r) := by
  obtain ⟨eta,heta,hlocal⟩ := uniform_curve_step F hβ hres hparent hlam hlam1 hT hT1
  let N : ℕ := ⌈(T-3/4)/eta⌉₊+1
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  let step : ℝ := (T-3/4)/(N:ℝ)
  have hstep0 : 0 ≤ step := div_nonneg (by linarith) hN.le
  have hNstep : (N:ℝ)*step = T-3/4 := by
    dsimp [step]
    field_simp
  have hstep : step ≤ eta := by
    dsimp [step]
    rw [div_le_iff₀ hN]
    have hc : (T-3/4)/eta ≤ (⌈(T-3/4)/eta⌉₊:ℝ) := Nat.le_ceil _
    have hm := mul_le_mul_of_nonneg_right hc heta.le
    rw [div_mul_cancel₀ _ heta.ne'] at hm
    dsimp [N]
    push_cast
    nlinarith
  let grid : ℕ → ℝ := fun j => T-(j:ℝ)*step
  have hgrid (j : ℕ) (hj : j ≤ N) : grid j ∈ Icc (3/4:ℝ) T := by
    have hj' : (j:ℝ) ≤ (N:ℝ) := by exact_mod_cast hj
    have hm := mul_le_mul_of_nonneg_right hj' hstep0
    have hp := mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) hstep0
    dsimp [grid]
    constructor <;> linarith
  have hgridN : grid N = 3/4 := by dsimp [grid]; linarith
  have hsucc (j : ℕ) : grid (j+1) = grid j-step := by
    dsimp [grid]
    push_cast
    ring
  have hseed : AnchorAt T (Curve.W lam T T) := by
    have h := native_seed_of_reserve hres (by linarith : (7/10:ℝ) ≤ T)
      (by linarith : T < 1)
    simpa only [Curve.W_seed lam (by linarith : (2/3:ℝ) < T)] using h
  have hcover : ∀ j : ℕ, j ≤ N → ∀ x ∈ Icc (grid j) T,
      AnchorAt x (Curve.W lam T x) := by
    intro j
    induction j with
    | zero =>
      intro hj x hx
      have heq : x=T := le_antisymm hx.2 (by simpa only [grid,Nat.cast_zero,zero_mul,sub_zero] using hx.1)
      simpa only [heq] using hseed
    | succ j ih =>
      intro hj x hx
      have hj0 : j ≤ N := Nat.le_of_succ_le hj
      have hR := hgrid j hj0
      by_cases hxj : grid j ≤ x
      · exact ih hj0 x ⟨hxj,hx.2⟩
      · have hxlo : 3/4 ≤ x := (hgrid (j+1) hj).1.trans hx.1
        have hxR : x ≤ grid j := (lt_of_not_ge hxj).le
        have hlength : grid j-x ≤ eta := by
          have hl := hx.1
          rw [hsucc] at hl
          linarith
        exact hlocal (grid j) x hR ⟨hxlo,hxR⟩ hlength
          (ih hj0 (grid j) ⟨le_rfl,hR.2⟩)
          (fun y hy hyT => ih hj0 y ⟨hy.le,hyT⟩)
  intro r hr
  exact hcover N le_rfl r (by simpa only [hgridN] using hr)

end
end Qrh.TwoSlot.AnchorContinuum
