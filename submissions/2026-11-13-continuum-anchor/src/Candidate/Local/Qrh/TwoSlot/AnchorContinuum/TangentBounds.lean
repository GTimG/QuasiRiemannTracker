/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Rational enclosures for the exact tangent, derived from the isolated root. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactTangent

set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section

theorem width_tight : (37616102690677/50000000000000:ℝ) < width ∧
    width < 15046441076271/20000000000000 := by
  have ht := theta_isolated
  have hd : 9*(12*theta-11) < 0 := by have hh := theta_range.2; linarith
  unfold width widthFrom
  constructor
  · apply (lt_div_iff_of_neg hd).mpr
    norm_num [lower,upper] at ht
    linarith [ht.1,ht.2]
  · apply (div_lt_iff_of_neg hd).mpr
    norm_num [lower,upper] at ht
    linarith [ht.1,ht.2]

theorem tangentIntercept_formula : tangentIntercept =
    (-90*width^2+145*width-170/3)/((45*width-14)*(15*width-10)) := by
  have hw := width_range
  have h1 : -14+width*45 ≠ 0 := by linarith
  have h2 : -10+width*15 ≠ 0 := by linarith
  have h3 : width ≠ 0 := by linarith
  have h4 : 140-width*660+width^2*675 ≠ 0 := by
    have he : 140-width*660+width^2*675 = (-14+width*45)*(-10+width*15) := by ring
    rw [he]
    exact mul_ne_zero h1 h2
  unfold tangentIntercept
  rw [tangentSlope_formula]
  unfold gain gainFrom
  ring_nf
  field_simp [h1,h2,h3,h4]
  <;> ring

theorem negative_slope_formula : -tangentSlope =
    ((675/2)*width^3-330*width^2-25*width+190/3)/
      (width*(45*width-14)*(15*width-10)) := by
  have hw := width_range
  have h1 : -14+width*45 ≠ 0 := by linarith
  have h2 : -10+width*15 ≠ 0 := by linarith
  have h3 : width ≠ 0 := by linarith
  have h4 : 140-width*660+width^2*675 ≠ 0 := by
    have he : 140-width*660+width^2*675 = (-14+width*45)*(-10+width*15) := by ring
    rw [he]
    exact mul_ne_zero h1 h2
  rw [tangentSlope_formula]
  unfold gain gainFrom
  ring_nf
  field_simp [h1,h2,h3,h4]
  <;> ring

theorem tangent_coefficient_bounds :
    (5805911/100000000:ℝ) < tangentIntercept ∧ tangentIntercept < 5805913/100000000 ∧
    (3799809/50000000:ℝ) < -tangentSlope ∧ -tangentSlope < 379981/5000000 := by
  have hw := width_tight
  have hpos : (0:ℝ) ≤ 37616102690677/50000000000000 := by norm_num
  have h2lo := pow_le_pow_left₀ hpos hw.1.le 2
  have h2hi := pow_le_pow_left₀ (hpos.trans hw.1.le) hw.2.le 2
  have h3lo := pow_le_pow_left₀ hpos hw.1.le 3
  have h3hi := pow_le_pow_left₀ (hpos.trans hw.1.le) hw.2.le 3
  have hd : 0 < (45*width-14)*(15*width-10) :=
    mul_pos (by linarith [hw.1]) (by linarith [hw.1])
  have hs : 0 < width*(45*width-14)*(15*width-10) :=
    mul_pos (mul_pos (by linarith [hw.1]) (by linarith [hw.1])) (by linarith [hw.1])
  rw [tangentIntercept_formula,negative_slope_formula]
  refine ⟨(lt_div_iff₀ hd).mpr ?_,(div_lt_iff₀ hd).mpr ?_,
    (lt_div_iff₀ hs).mpr ?_,(div_lt_iff₀ hs).mpr ?_⟩ <;>
    nlinarith [hw.1,hw.2,h2lo,h2hi,h3lo,h3hi]

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
