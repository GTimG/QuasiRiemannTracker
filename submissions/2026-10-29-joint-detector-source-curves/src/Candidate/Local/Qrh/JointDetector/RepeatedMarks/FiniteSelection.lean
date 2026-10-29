/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A rowwise choice from a fixed finite dictionary is paid only after
applying the moment theorem to each fixed member. No rowwise coefficient
choice is inserted into an analytic source theorem. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

/-- A finite multiplicity partition costs its fixed cardinality in an
energy bound. This applies to all Sobolev derivatives with the same choice. -/
theorem rowwise_selection_energy {Row Choice : Type*} [Fintype Choice]
    (rows : Finset Row) (F : Choice → Row → ℂ) (choose : Row → Choice) (bound : ℝ)
    (h : ∀ c : Choice, (∑ u ∈ rows, ‖F c u‖^2) ≤ bound) :
    (∑ u ∈ rows, ‖F (choose u) u‖^2) ≤ (Fintype.card Choice:ℝ)*bound := by
  calc _ ≤ ∑ u ∈ rows, ∑ c : Choice, ‖F c u‖^2 := by
        apply Finset.sum_le_sum
        intro u hu
        exact Finset.single_le_sum (fun c _ => sq_nonneg ‖F c u‖) (Finset.mem_univ _)
    _ = ∑ c : Choice, ∑ u ∈ rows, ‖F c u‖^2 := Finset.sum_comm
    _ ≤ ∑ _c : Choice, bound := Finset.sum_le_sum (fun c _ => h c)
    _ = _ := by simp

/-- The same argument works with fixed multiplicity dictionaries whose
members have different later constants: the finite sum is chosen after the
slot data, while no dependence on the asymptotic scale is introduced. -/
theorem rowwise_selection_energy_constants {Row Choice : Type*} [Fintype Choice]
    (rows : Finset Row) (F : Choice → Row → ℂ) (choose : Row → Choice)
    (C : Choice → ℝ) (U exponent : ℝ)
    (h : ∀ c : Choice, (∑ u ∈ rows, ‖F c u‖^2) ≤ C c*U^exponent) :
    (∑ u ∈ rows, ‖F (choose u) u‖^2) ≤ (∑ c : Choice, C c)*U^exponent := by
  calc _ ≤ ∑ u ∈ rows, ∑ c : Choice, ‖F c u‖^2 := by
        apply Finset.sum_le_sum
        intro u hu
        exact Finset.single_le_sum (fun c _ => sq_nonneg ‖F c u‖) (Finset.mem_univ _)
    _ = ∑ c : Choice, ∑ u ∈ rows, ‖F c u‖^2 := Finset.sum_comm
    _ ≤ ∑ c : Choice, C c*U^exponent := Finset.sum_le_sum (fun c _ => h c)
    _ = _ := by rw [Finset.sum_mul]

end
end Qrh.JointDetector.RepeatedMarks
