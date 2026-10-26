import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Arithmetic.LocalReserves
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Cycle61.Moment
noncomputable section
open Arithmetic

/-- The original total slot width selects the amplifier once. -/
def originalCell (t : ℝ) : ℕ := max 1 ⌈(t - 17/500)*100000⌉₊

theorem originalCell_mem {t : ℝ} (ht : 17/500 ≤ t ∧ t ≤ 1/25) :
    1 ≤ originalCell t ∧ originalCell t ≤ 600 ∧
      cellUpper (originalCell t) - 1/100000 ≤ t ∧
      t ≤ cellUpper (originalCell t) := by
  have hx : 0 ≤ (t - 17/500)*100000 := by linarith [ht.1]
  have hc : ⌈(t - 17/500)*100000⌉₊ ≤ 600 :=
    Nat.ceil_le.mpr (by norm_num; linarith [ht.2])
  have hle := Nat.le_ceil ((t - 17/500)*100000)
  have hlt := Nat.ceil_lt_add_one hx
  have hi : 1 ≤ originalCell t := le_max_left _ _
  have hi' : originalCell t ≤ 600 := max_le (by omega) hc
  refine ⟨hi, hi', ?_, ?_⟩
  · by_cases hc1 : ⌈(t - 17/500)*100000⌉₊ ≤ 1
    · simp only [originalCell, max_eq_left hc1, cellUpper, Nat.cast_one]
      linarith [ht.1]
    · simp only [originalCell, max_eq_right (by omega :
        1 ≤ ⌈(t - 17/500)*100000⌉₊), cellUpper]
      linarith
  · have hcast : (⌈(t - 17/500)*100000⌉₊ : ℝ) ≤ (originalCell t : ℝ) := by
      exact_mod_cast (le_max_right 1 ⌈(t - 17/500)*100000⌉₊)
    unfold cellUpper
    linarith

theorem normalized_cell_bounds {M n₁ n₂ z : ℝ} (hM : 0 < M)
    (hz : (17/500)*M ≤ z ∧ z ≤ (1/25)*M)
    (haffine : n₁+n₂+lambda*z ≤ B*M) :
    let j := originalCell (z/M)
    1 ≤ j ∧ j ≤ 600 ∧
      max (n₁+n₂+(9/2)*z-M) 0 ≤ M*g (cellUpper j) ∧
      n₁+n₂+z ≤ M*totalA (cellUpper j) ∧
      0 < M*amp (cellUpper j) := by
  dsimp only
  have ht : 17/500 ≤ z/M ∧ z/M ≤ 1/25 := by
    constructor
    · exact (le_div_iff₀ hM).mpr hz.1
    · exact (div_le_iff₀ hM).mpr hz.2
  obtain ⟨hj1,hj600,hl,hu⟩ := originalCell_mem ht
  have hb := cellUpper_bounds hj1 hj600
  have hzup : z ≤ cellUpper (originalCell (z/M))*M := (div_le_iff₀ hM).mp hu
  have hzlow : (cellUpper (originalCell (z/M))-1/100000)*M ≤ z :=
    (le_div_iff₀ hM).mp hl
  have hcoef : 0 ≤ (9/2:ℝ)-lambda := by norm_num [lambda]
  have hcoef' : 0 ≤ lambda-1 := by norm_num [lambda]
  have hdef := mul_le_mul_of_nonneg_left hzup hcoef
  have htotal := mul_le_mul_of_nonneg_left hzlow hcoef'
  have hg := g_pos hb
  have hamp := amp_pos hb
  refine ⟨hj1,hj600, max_le ?_ (mul_pos hM hg).le, ?_, mul_pos hM hamp⟩
  · unfold g
    nlinarith
  · unfold totalA
    nlinarith

theorem comparison_old_capacity {M z ξ : ℝ}
    (hz : z ≤ M/25) (hξ : ξ ≤ 7*M/100) :
    M/4 + (M/2+ξ) + (9/2)*z ≤ M := by linarith

#print axioms originalCell_mem
#print axioms normalized_cell_bounds
end
end Cycle61.Moment
