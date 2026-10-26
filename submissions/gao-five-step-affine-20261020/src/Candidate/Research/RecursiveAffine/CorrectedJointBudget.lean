/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.JointBudget

set_option autoImplicit false
namespace Cycle153
noncomputable section
open Cycle63.Optimization

/-- The cost that the actual valuation-cone estimate retains for common
reduction. Common reduction is not paid twice as a pure length saving. -/
def commonLoss (q : ℝ) : ℝ := max (3/19) (4*density q-5/4)

def correctedJointBudget (q W L ampl previousPayment V Red : ℝ) : ℝ :=
  jointBudget q W L ampl previousPayment+
    ((1-density q)-commonLoss q)*V-commonLoss q*Red

theorem density_antitone {q₀ q : ℝ} (hq₀ : q₀≤q) (hq : q≤3/4) :
    density q≤density q₀ := by
  have hd : 0<5-2*q := by linarith
  have hd₀ : 0<5-2*q₀ := by linarith
  have hi := jointBudget_increment (W:=1) (L:=0) (ampl:=0) (previousPayment:=0) hq hq₀
  have hm : 0≤((50/3:ℝ)*1/((5-2*q)*(5-2*q₀))-0)*(q-q₀) :=
    mul_nonneg (by
      simp only [mul_one,sub_zero]
      exact div_nonneg (by norm_num) (mul_nonneg hd.le hd₀.le)) (sub_nonneg.mpr hq₀)
  simp only [jointBudget, mul_one, mul_zero, sub_zero, add_zero] at hi
  linarith only [hi,hm]

theorem commonLoss_antitone {q₀ q : ℝ} (hq₀ : q₀≤q) (hq : q≤3/4) :
    commonLoss q≤commonLoss q₀ := by
  unfold commonLoss
  apply max_le_max le_rfl
  linarith [density_antitone hq₀ hq]

/-- A finite negative reduction error costs its actual multiplier mass.
The old growth certificate is sufficient: both corrected coefficients are
nondecreasing in the terminal bin, apart from that paid finite error. -/
theorem correctedJointBudget_all_bins {q₀ q W L ampl previousPayment V Red eta E : ℝ}
    (hq₀ : q₀≤q) (hq : q≤3/4) (hW : 0≤W) (hV : 0≤V) (hRed : -E≤Red)
    (hgrowth : eta≤((50/3)/(5-2*q₀)^2)*W-L) :
    correctedJointBudget q₀ W L ampl previousPayment V Red+
      eta*(q-q₀)-E*(commonLoss q₀-commonLoss q)≤
      correctedJointBudget q W L ampl previousPayment V Red := by
  have hb := jointBudget_all_bins (ampl:=ampl) (previousPayment:=previousPayment) hq₀ hq hW hgrowth
  have hrho := density_antitone hq₀ hq
  have hh := commonLoss_antitone hq₀ hq
  have hvm : 0≤(((1-density q)-commonLoss q)-((1-density q₀)-commonLoss q₀))*V :=
    mul_nonneg (by linarith only [hrho,hh]) hV
  have hrm := mul_le_mul_of_nonneg_left hRed (sub_nonneg.mpr hh)
  unfold correctedJointBudget
  nlinarith only [hb,hvm,hrm]

theorem correctedJointBudget_uniform_reserve {q₀ q W L ampl previousPayment V Red eta reserve : ℝ}
    (hq₀ : q₀≤q) (hq : q≤3/4) (hW : 0≤W) (hV : 0≤V) (hRed : 0≤Red)
    (heta : 0≤eta) (hjunction : reserve<correctedJointBudget q₀ W L ampl previousPayment V Red)
    (hgrowth : eta≤((50/3)/(5-2*q₀)^2)*W-L) :
    reserve<correctedJointBudget q W L ampl previousPayment V Red := by
  have hb := correctedJointBudget_all_bins (ampl:=ampl) (previousPayment:=previousPayment)
    (E:=0) hq₀ hq hW hV (by simpa using hRed) hgrowth
  have hm : 0≤eta*(q-q₀) := mul_nonneg heta (sub_nonneg.mpr hq₀)
  linarith only [hb,hm,hjunction]

end
end Cycle153

#print axioms Cycle153.correctedJointBudget_all_bins
