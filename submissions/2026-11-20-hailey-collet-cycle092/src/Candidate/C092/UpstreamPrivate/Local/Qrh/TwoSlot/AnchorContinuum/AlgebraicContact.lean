/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The exact algebraic contact and its rational isolating interval. These are
scalar facts; the limiting analytic return is a separate obligation. -/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Set

def polynomial (x : ℝ) : ℝ :=
  3888*19^5*(15*x-13)^4*(1-x)^5-7*(7-6*x)^4*(9*x-7)^5

def lower : ℝ := 109168232013339822100148/125000000000000000000000
def upper : ℝ := 174669171221343715360237/200000000000000000000000

theorem lower_negative : polynomial lower < 0 := by norm_num [polynomial,lower]
theorem upper_positive : 0 < polynomial upper := by norm_num [polynomial,upper]

theorem exists_isolated_root : ∃ x ∈ Ioo lower upper, polynomial x = 0 := by
  have hcont : Continuous polynomial := by unfold polynomial; fun_prop
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc
    (by norm_num [lower,upper] : lower ≤ upper) hcont.continuousOn
    (show (0:ℝ) ∈ Icc (polynomial lower) (polynomial upper) from
      ⟨lower_negative.le,upper_positive.le⟩)
  refine ⟨x,⟨?_,?_⟩,hzero⟩
  · by_contra hn
    have he : x = lower := le_antisymm (le_of_not_gt hn) hx.1
    subst x
    linarith [lower_negative]
  · by_contra hn
    have he : x = upper := le_antisymm hx.2 (le_of_not_gt hn)
    subst x
    linarith [upper_positive]

def theta : ℝ := Classical.choose exists_isolated_root

theorem theta_isolated : theta ∈ Ioo lower upper :=
  (Classical.choose_spec exists_isolated_root).1
theorem theta_root : polynomial theta = 0 :=
  (Classical.choose_spec exists_isolated_root).2

theorem theta_range : theta ∈ Ioo (13/15:ℝ) (7/8) := by
  have h := theta_isolated
  norm_num [lower,upper] at h
  constructor <;> linarith [h.1,h.2]

theorem theta_lt_rational_target : theta < (4366729281/5000000000:ℝ) := by
  have h := theta_isolated.2
  norm_num [upper] at h
  linarith

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.theta_root
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.theta_isolated
