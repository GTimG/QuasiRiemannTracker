/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The exact critical density and short/long count balance. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactWidth

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section

def density : ℝ := (45*width-14)/(54*width+6)
def count : ℝ := 5/9+density/6

theorem density_range : (2129/5000:ℝ) < density ∧ density < 4259/10000 := by
  have hw := width_range
  have hd : 0 < 54*width+6 := by linarith
  unfold density
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith [hw.1]
  · apply (div_lt_iff₀ hd).mpr
    linarith [hw.2]

theorem short_balance : 1-density*((1+width)/2+ideal width) = count := by
  rw [←gain_eq_ideal]
  have hw := width_range
  have hd : 54*width+6 ≠ 0 := by linarith
  have hg : 45*width-14 ≠ 0 := by linarith
  have hn : 6+width*54 ≠ 0 := by intro h; apply hd; linarith
  have hm : -14+width*45 ≠ 0 := by intro h; apply hg; linarith
  unfold count density gain gainFrom
  ring_nf
  field_simp [hd,hg,hn,hm]
  <;> ring

theorem long_balance : 1/6+(3/2)*(5/6-density)*width = count := by
  have hw := width_range
  have hd : 54*width+6 ≠ 0 := by linarith
  have hn : 6+width*54 ≠ 0 := by intro h; apply hd; linarith
  unfold count density
  ring_nf
  field_simp [hd,hn]
  <;> ring

theorem theta_density_relation : theta*(18+24*density) = 14+25*density := by
  have hw := width_range
  have hd : 54*width+6 ≠ 0 := by linarith
  have ht := theta_range
  have hx : 12*theta-11 ≠ 0 := by linarith [ht.2]
  have hwidth : width*(9*(12*theta-11)) = 12*theta-14 := by
    unfold width widthFrom
    field_simp [hx]
  unfold density
  have hn : 6+width*54 ≠ 0 := by intro h; apply hd; linarith
  ring_nf
  field_simp [hd,hn]
  nlinarith [hwidth]

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.short_balance
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.long_balance
