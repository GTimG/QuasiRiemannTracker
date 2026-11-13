/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Exact transport from the contact polynomial to the active source width and
the ideal gain. No endpoint nonvanishing assertion is made here. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactUniqueness
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.IdealCurve

set_option autoImplicit false
set_option maxHeartbeats 10000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section

def widthFrom (x : ℝ) : ℝ := (12*x-14)/(9*(12*x-11))
def width : ℝ := widthFrom theta
def widthPolynomial (w : ℝ) : ℝ :=
  19^5*(3*w-2)^4*(9*w+2)^5-567*w^4*(45*w-14)^5

theorem width_substitution {x : ℝ} (hx : 12*x-11 ≠ 0) :
    widthPolynomial (widthFrom x)*(12*x-11)^9 = -49152*polynomial x := by
  unfold widthPolynomial widthFrom polynomial
  field_simp [hx]
  <;> ring

theorem width_range : (7523/10000:ℝ) < width ∧ width < 1881/2500 := by
  have ht := theta_isolated
  have hd : 9*(12*theta-11) < 0 := by
    have hh := theta_range.2
    linarith
  unfold width widthFrom
  constructor
  · apply (lt_div_iff_of_neg hd).mpr
    norm_num [lower,upper] at ht
    linarith [ht.1,ht.2]
  · apply (div_lt_iff_of_neg hd).mpr
    norm_num [lower,upper] at ht
    linarith [ht.1,ht.2]

theorem width_root : widthPolynomial width = 0 := by
  have hd : 12*theta-11 ≠ 0 := by have ht := theta_range.2; linarith
  have hh := width_substitution hd
  rw [theta_root,mul_zero] at hh
  have hn : (12*theta-11)^9 ≠ 0 := pow_ne_zero _ hd
  exact (mul_eq_zero.mp hh).resolve_right hn

def gainFrom (w : ℝ) : ℝ := (w+12-(45/2)*w^2)/(45*w-14)
def gain : ℝ := gainFrom width

theorem gain_polynomial_identity {w : ℝ} (hw : 45*w-14 ≠ 0) :
    ((Curve.P w-gainFrom w)^5-(5/16:ℝ)^5*7*w^4*(w-2/3))*(45*w-14)^5 =
      (5/48:ℝ)^5*(3*w-2)*widthPolynomial w := by
  unfold Curve.P gainFrom widthPolynomial
  have hn : -14+w*45 ≠ 0 := by intro h; apply hw; linarith
  ring_nf
  field_simp [hw,hn]
  <;> ring

theorem gain_eq_ideal : gain = ideal width := by
  have hr := width_range
  have hd : 45*width-14 ≠ 0 := by linarith
  have hh := gain_polynomial_identity hd
  rw [width_root,mul_zero] at hh
  have he : (Curve.P width-gain)^5 = (5/16:ℝ)^5*7*width^4*(width-2/3) := by
    have hz := (mul_eq_zero.mp hh).resolve_right (pow_ne_zero 5 hd)
    change (Curve.P width-gainFrom width)^5 = _
    linarith
  have hi := ideal_gap_pow_five (r := width) (by linarith)
  have hp : (Curve.P width-gain)^5 = (Curve.P width-ideal width)^5 := he.trans hi.symm
  have hinj := (show Odd (5:ℕ) by decide).pow_injective hp
  linarith

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.width_root
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.gain_eq_ideal
