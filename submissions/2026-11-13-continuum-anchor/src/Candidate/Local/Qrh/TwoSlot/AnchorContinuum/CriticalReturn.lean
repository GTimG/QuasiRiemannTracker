/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Identify the admitted exact count at contact and the zero of the limiting
physical margin. The complete return and positive-cost passage are separate. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactCountScheme

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Set
open Qrh.TwoSlot.AnchorZeroLoss.Affine.Return

theorem critical_density_admitted : density ∈ Icc (189/512:ℝ) (15/32) := by
  have hd := density_range
  constructor <;> linarith [hd.1,hd.2]

theorem critical_denominator_pos : 0 < ExactWindow.JI density (1/2) :=
  ExactWindow.hJ critical_density_admitted ⟨by norm_num,le_rfl⟩

theorem crossing_at_contact : ExactWindow.crossingI density (1/2) = width := by
  have hs := short_balance
  have hl := long_balance
  rw [←gain_eq_ideal] at hs
  have he : 2*ExactWindow.TI density (1/2) = width*(3*ExactWindow.JI density (1/2)) := by
    unfold ExactWindow.TI ExactWindow.JI ExactWindow.UI ExactWindow.kI exactLine tangentIntercept
    nlinarith only [hs,hl]
  unfold ExactWindow.crossingI
  apply (div_eq_iff (mul_ne_zero (by norm_num) critical_denominator_pos.ne')).mpr
  exact he

theorem value_at_contact : ExactWindow.valueI density (1/2) = count := by
  have hh := ExactWindow.inverse_identity density (1/2) critical_denominator_pos.ne'
  rw [crossing_at_contact] at hh
  have he : 1-density*((1/2)*(1+2*exactLine.g0)+
      (1-(1/2)*(1+2*exactLine.g1))*width) = 1-density*((1+width)/2+gain) := by
    unfold exactLine tangentIntercept
    ring
  rw [he,gain_eq_ideal,short_balance] at hh
  exact hh.symm

theorem numerator_at_contact : ExactWindow.NI density (1/2) = count*ExactWindow.JI density (1/2) := by
  have hh := value_at_contact
  unfold ExactWindow.valueI at hh
  exact (div_eq_iff critical_denominator_pos.ne').mp hh

def ell : ℝ := 11/3-4*theta
def baseCost (h d p : ℝ) : ℝ :=
  1/2+ell/2-5*h/12+d/2+d*p*(2*ell-h/4)
def margin (h d p : ℝ) : ℝ :=
  ExactWindow.JI d p*(theta-baseCost h d p)-(3/4)*h*ExactWindow.NI d p

def targetMargin (target h d p : ℝ) : ℝ :=
  ExactWindow.JI d p*(target-(1/2+(11/3-4*target)/2-5*h/12+d/2+
    d*p*(2*(11/3-4*target)-h/4)))-(3/4)*h*ExactWindow.NI d p

/-- Exact, uniform dependence on the proposed endpoint. The source line and
conductor cutoff stay fixed while the endpoint geometry changes coherently. -/
theorem target_shift (target h d p : ℝ) :
    targetMargin target h d p = margin h d p+
      ExactWindow.JI d p*(3+8*d*p)*(target-theta) := by
  unfold targetMargin margin baseCost ell
  ring

/-- At the critical row, the conductor-cutoff coefficient cancels exactly. -/
theorem critical_return_balance (h : ℝ) : theta-baseCost h density (1/2)-(3/4)*h*count = 0 := by
  unfold baseCost ell count
  nlinarith only [theta_density_relation]

theorem margin_at_contact (h : ℝ) : margin h density (1/2) = 0 := by
  unfold margin
  rw [numerator_at_contact]
  calc
    _ = ExactWindow.JI density (1/2)*(theta-baseCost h density (1/2)-(3/4)*h*count) := by ring
    _ = 0 := by rw [critical_return_balance]; ring

theorem critical_target_margin_pos {target : ℝ} (ht : theta < target) (h : ℝ) :
    0 < targetMargin target h density (1/2) := by
  rw [target_shift,margin_at_contact,zero_add]
  have hd := density_range.1
  exact mul_pos (mul_pos critical_denominator_pos (by linarith)) (sub_pos.mpr ht)

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.value_at_contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.margin_at_contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.critical_target_margin_pos
