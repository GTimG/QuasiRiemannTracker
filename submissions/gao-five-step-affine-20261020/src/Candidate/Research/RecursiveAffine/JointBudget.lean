/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalLedger

set_option autoImplicit false
namespace Cycle153
noncomputable section
open Cycle63.Optimization

/-- One terminal HIGH bin after all earlier LOW deletions. W is the
outgoing width and L the retained source length. Amplification and the
previous deletion payments appear once each. -/
def jointBudget (q W L ampl previousPayment : ℝ) : ℝ :=
  (1-density q)*W-q*L+ampl-previousPayment

theorem jointBudget_identity (q rootLength missing reduction deletion ampl previousPayment : ℝ) :
    (1-density q)-q*rootLength+q*deletion-previousPayment-
      (5-6*density q)*ampl+(q-(1-density q))*missing+q*reduction =
    jointBudget q (1-missing-6*ampl)
      (rootLength-missing-reduction-deletion) ampl previousPayment := by
  unfold jointBudget
  ring

theorem jointBudget_increment {q q₀ W L ampl previousPayment : ℝ}
    (hq : q≤3/4) (hq₀ : q₀≤q) :
    jointBudget q W L ampl previousPayment-jointBudget q₀ W L ampl previousPayment =
      ((50/3)*W/((5-2*q)*(5-2*q₀))-L)*(q-q₀) := by
  have hd : 5-2*q≠0 := by linarith
  have hd₀ : 5-2*q₀≠0 := by linarith
  unfold jointBudget density
  field_simp [hd,hd₀]
  ring_nf
  field_simp [hd,hd₀]
  have hinv := mul_inv_cancel₀ (show (5-q*2:ℝ)≠0 by linarith)
  linear_combination (10*W*q₀)*hinv

/-- The exact junction and growth certificates pay every later bin. A
finite junction check is not substituted for a continuum of HIGH bins. -/
theorem jointBudget_all_bins {q₀ q W L ampl previousPayment eta : ℝ}
    (hq₀ : q₀≤q) (hq : q≤3/4) (hW : 0≤W)
    (hgrowth : eta≤((50/3)/(5-2*q₀)^2)*W-L) :
    jointBudget q₀ W L ampl previousPayment+eta*(q-q₀)≤
      jointBudget q W L ampl previousPayment := by
  have hd : 0<5-2*q := by linarith
  have hd₀ : 0<5-2*q₀ := by linarith
  have hden : (5-2*q)*(5-2*q₀)≤(5-2*q₀)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : 5-2*q≤5-2*q₀) hd₀.le]
  have hc : (50/3)*W/(5-2*q₀)^2≤(50/3)*W/((5-2*q)*(5-2*q₀)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hd hd₀) hden
  have hh : eta≤(50/3)*W/((5-2*q)*(5-2*q₀))-L := by
    have he : (50/3)*W/(5-2*q₀)^2=((50/3)/(5-2*q₀)^2)*W := by ring
    rw [he] at hc
    linarith only [hgrowth,hc]
  have hm := mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hq₀)
  have hi := jointBudget_increment (W:=W) (L:=L) (ampl:=ampl) (previousPayment:=previousPayment) hq hq₀
  linarith only [hm,hi]

theorem jointBudget_uniform_reserve {q₀ q W L ampl previousPayment eta reserve : ℝ}
    (hq₀ : q₀≤q) (hq : q≤3/4) (hW : 0≤W) (heta : 0≤eta)
    (hjunction : reserve<jointBudget q₀ W L ampl previousPayment)
    (hgrowth : eta≤((50/3)/(5-2*q₀)^2)*W-L) :
    reserve<jointBudget q W L ampl previousPayment := by
  have hb := jointBudget_all_bins (ampl:=ampl) (previousPayment:=previousPayment) hq₀ hq hW hgrowth
  have hm : 0≤eta*(q-q₀) := mul_nonneg heta (sub_nonneg.mpr hq₀)
  linarith only [hb,hm,hjunction]

end
end Cycle153

#print axioms Cycle153.jointBudget_uniform_reserve
