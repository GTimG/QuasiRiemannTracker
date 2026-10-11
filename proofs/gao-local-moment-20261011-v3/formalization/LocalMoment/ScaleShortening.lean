import Mathlib.Tactic

/-!
Arithmetic geometry only.  This file does not assume or prove an analytic
moment estimate.  Its dichotomy identifies which of two separately established
moment estimates would apply to each shortened physical scale.
-/

namespace LocalMomentV3Review

theorem audited_upper_edges :
    (402041377237 / 952737117000 : ℝ) < 211 / 500 ∧
    (948498980500 / 26750087198289 : ℝ) < 71 / 2000 ∧
    (74327181263 / 2142705776133 : ℝ) > 3 / 100 := by
  norm_num

theorem incumbent_of_short_plain (x₁ x₂ z : ℝ)
    (hx₁ : x₁ ≤ 211 / 500) (hx₂ : x₂ ≤ 211 / 500)
    (hz : z ≤ 71 / 2000)
    (hshort : x₁ ≤ 41 / 100 ∨ x₂ ≤ 41 / 100) :
    x₁ + x₂ + (9 / 2) * z ≤ 1 - 33 / 4000 := by
  rcases hshort with h | h <;> linarith

theorem shortened_scale_dichotomy (n x₁ x₂ z : ℝ)
    (hn : n ≤ 211 / 500)
    (hx₁ : x₁ ≤ n) (hx₂ : x₂ ≤ n)
    (hzlow : 3 / 100 ≤ z) (hzhigh : z ≤ 71 / 2000)
    (hcap : 2 * n + (2249 / 500) * z ≤ 1) :
    ((41 / 100 ≤ x₁ ∧ x₁ ≤ 11 / 25) ∧
     (41 / 100 ≤ x₂ ∧ x₂ ≤ 11 / 25) ∧
     (3 / 100 ≤ z ∧ z ≤ 1 / 25) ∧
     x₁ + x₂ + (2249 / 500) * z ≤ 1) ∨
    (x₁ + x₂ + (9 / 2) * z ≤ 1 - 33 / 4000) := by
  by_cases hshort : x₁ ≤ 41 / 100 ∨ x₂ ≤ 41 / 100
  · exact Or.inr (incumbent_of_short_plain x₁ x₂ z
      (hx₁.trans hn) (hx₂.trans hn) hzhigh hshort)
  · push Not at hshort
    left
    refine ⟨⟨hshort.1.le, ?_⟩, ⟨hshort.2.le, ?_⟩,
      ⟨hzlow, ?_⟩, ?_⟩ <;> linarith

theorem incumbent_of_short_slots (x₁ x₂ z : ℝ)
    (hx₁ : x₁ ≤ 211 / 500) (hx₂ : x₂ ≤ 211 / 500)
    (hz : z ≤ 3 / 100) :
    x₁ + x₂ + (9 / 2) * z ≤ 1 - 21 / 1000 := by
  linarith

/-- Actual selected width may be arbitrarily smaller than its target capacity.
The smaller width is handled by the existing moment with a strict reserve. -/
theorem shortened_scale_and_slot_dichotomy (n x₁ x₂ z : ℝ)
    (hn : n ≤ 211 / 500)
    (hx₁ : x₁ ≤ n) (hx₂ : x₂ ≤ n)
    (hzhigh : z ≤ 71 / 2000)
    (hcap : 2 * n + (2249 / 500) * z ≤ 1) :
    ((41 / 100 ≤ x₁ ∧ x₁ ≤ 11 / 25) ∧
     (41 / 100 ≤ x₂ ∧ x₂ ≤ 11 / 25) ∧
     (3 / 100 ≤ z ∧ z ≤ 1 / 25) ∧
     x₁ + x₂ + (2249 / 500) * z ≤ 1) ∨
    (x₁ + x₂ + (9 / 2) * z ≤ 1 - 33 / 4000) := by
  by_cases hz : z ≤ 3 / 100
  · right
    have h := incumbent_of_short_slots x₁ x₂ z
      (hx₁.trans hn) (hx₂.trans hn) hz
    linarith
  · exact shortened_scale_dichotomy n x₁ x₂ z hn hx₁ hx₂
      (le_of_not_ge hz) hzhigh hcap

/-- A full-positive-supply branch keeps target-capacity gain even when its
physical width is short. Zero-gain factors must not be included in this product. -/
theorem positive_supply_retains_target_gain (q target total : ℝ)
    (hq : 0 ≤ q) (hsupply : target ≤ total) :
    2 * q * target ≤ 2 * q * total := by
  nlinarith

#print axioms audited_upper_edges
#print axioms incumbent_of_short_plain
#print axioms shortened_scale_dichotomy
#print axioms incumbent_of_short_slots
#print axioms shortened_scale_and_slot_dichotomy
#print axioms positive_supply_retains_target_gain

end LocalMomentV3Review
