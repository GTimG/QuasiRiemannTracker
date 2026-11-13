/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The closest upper Farey neighbour of the continuum contact with numerator
at most 10^127-1, fitting the tracker's 256-character rational field.
Only scalar root comparisons are proved here, not exact-root nonvanishing. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ContactUniqueness

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace Qrh.TwoSlot.AnchorContinuum.ClosestRational
noncomputable section
open Set Contact

def numerator : ℕ :=
  9908119238306612133369374975000622988619121777878229799765263366946606045502455625911569003364955967645745531862430068266267717
def denominator : ℕ :=
  11345012023616779600791582323373494582287250283647959965785871011074347975117040113347744503437234376916434871293982689424818700
def target : ℝ := (numerator:ℝ)/denominator
def lowerNumerator : ℕ :=
  336084165510841864773293977341076535729191874784659739069235924217334553047945586430279659430167331736594209482641160401907041
def lowerDenominator : ℕ :=
  384823679142497733928459651611619429502318300936351834621101436720598407910134460595059350763273153920232672097274970191818153
def lowerTarget : ℝ := (lowerNumerator:ℝ)/lowerDenominator

/-- Fixed cost currently used by the existing physical return. -/
def cost : ℝ := 1/(100*(10:ℝ)^256)
def bufferedUpper : ℝ := target-256/(10:ℝ)^256

theorem farey_determinant : numerator*lowerDenominator-lowerNumerator*denominator = 1 := by
  norm_num [numerator,denominator,lowerNumerator,lowerDenominator]
theorem numerator_budget : numerator ≤ 10^127-1 ∧
    10^127-1 < numerator+lowerNumerator := by
  norm_num [numerator,lowerNumerator]
theorem lower_negative : polynomial lowerTarget < 0 := by
  norm_num [polynomial,lowerTarget,lowerNumerator,lowerDenominator]
theorem buffered_positive : 0 < polynomial bufferedUpper := by
  norm_num [polynomial,bufferedUpper,target,numerator,denominator]
theorem cost_pos : 0 < cost := by norm_num [cost]

/-- Exact rational certificate supplies a root below the buffered target;
uniqueness identifies it with the already defined scalar contact. -/
theorem contact_lt_buffered : theta < bufferedUpper := by
  have hcont : Continuous polynomial := by unfold polynomial; fun_prop
  have hlo : Contact.lower < bufferedUpper := by
    norm_num [Contact.lower,bufferedUpper,target,numerator,denominator]
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc hlo.le hcont.continuousOn
    (show (0:ℝ) ∈ Icc (polynomial Contact.lower) (polynomial bufferedUpper) from
      ⟨Contact.lower_negative.le,buffered_positive.le⟩)
  have hxlt : x < bufferedUpper := by
    by_contra hn
    have he : x = bufferedUpper := le_antisymm hx.2 (le_of_not_gt hn)
    subst x
    linarith [buffered_positive]
  have hxrange : x ∈ Ioo (13/15:ℝ) (7/8) := by
    have hrlo : (13/15:ℝ) < Contact.lower := by norm_num [Contact.lower]
    have hrhi : bufferedUpper < (7/8:ℝ) := by
      norm_num [bufferedUpper,target,numerator,denominator]
    exact ⟨hrlo.trans_le hx.1,hxlt.trans hrhi⟩
  rw [root_unique hxrange hzero] at hxlt
  exact hxlt

theorem target_gap : theta+25600*cost < target := by
  have hh := contact_lt_buffered
  have he : (25600:ℝ)*cost = 256/(10:ℝ)^256 := by norm_num [cost]
  rw [he]
  unfold bufferedUpper at hh
  linarith

theorem target_bounds : theta < target ∧ target ≤ (87334587/100000000:ℝ) := by
  constructor
  · linarith [target_gap,cost_pos]
  · norm_num [target,numerator,denominator]

end
end Qrh.TwoSlot.AnchorContinuum.ClosestRational
#print axioms Qrh.TwoSlot.AnchorContinuum.ClosestRational.target_gap
