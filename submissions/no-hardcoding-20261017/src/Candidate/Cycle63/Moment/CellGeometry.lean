import Candidate.Cycle63.Arithmetic.LocalReserves
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Cycle63.Moment
noncomputable section
open Arithmetic

/-- The original total slot width selects the amplifier once: the first cell whose upper edge is
at least the width. -/
def originalCell (t : ℝ) : ℕ := max 1 ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊

theorem originalCell_mem {t : ℝ}
    (ht : Cycle63.Optimization.slotFloor ≤ t ∧ t ≤ Cycle63.Optimization.slotTop) :
    1 ≤ originalCell t ∧ originalCell t ≤ Cycle63.Optimization.cellCount ∧
      cellUpper (originalCell t) - Cycle63.Optimization.cellMesh ≤ t ∧
      t ≤ cellUpper (originalCell t) := by
  have hm := Cycle63.Optimization.cellMesh_pos
  have hcm := Cycle63.Optimization.cellCount_mul
  have hx : 0 ≤ (t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh :=
    div_nonneg (by linarith [ht.1]) hm.le
  have hxm : (t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh*Cycle63.Optimization.cellMesh =
      t - Cycle63.Optimization.slotFloor := div_mul_cancel₀ _ hm.ne'
  have hc : ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊ ≤
      Cycle63.Optimization.cellCount := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hm]
    linarith [ht.2]
  have hle := Nat.le_ceil ((t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh)
  have hlt := Nat.ceil_lt_add_one hx
  have hi : 1 ≤ originalCell t := le_max_left _ _
  have hi' : originalCell t ≤ Cycle63.Optimization.cellCount :=
    max_le Cycle63.Optimization.one_le_cellCount hc
  refine ⟨hi, hi', ?_, ?_⟩
  · by_cases hc1 : ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊ ≤ 1
    · simp only [originalCell, max_eq_left hc1, cellUpper, Nat.cast_one]
      linarith [ht.1]
    · simp only [originalCell, max_eq_right (by omega :
        1 ≤ ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊), cellUpper]
      nlinarith [mul_lt_mul_of_pos_right hlt hm]
  · have hcast : (⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊ : ℝ) ≤
        (originalCell t : ℝ) := by
      exact_mod_cast (le_max_right 1 ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊)
    unfold cellUpper
    nlinarith [mul_le_mul_of_nonneg_right (hle.trans hcast) hm.le]

theorem normalized_cell_bounds {M n₁ n₂ z : ℝ} (hM : 0 < M)
    (hz : Cycle63.Optimization.slotFloor*M ≤ z ∧ z ≤ Cycle63.Optimization.slotTop*M)
    (haffine : n₁+n₂+lambda*z ≤ B*M) :
    let j := originalCell (z/M)
    1 ≤ j ∧ j ≤ Cycle63.Optimization.cellCount ∧
      max (n₁+n₂+(9/2)*z-M) 0 ≤ M*g (cellUpper j) ∧
      n₁+n₂+z ≤ M*totalA (cellUpper j) ∧
      0 < M*amp (cellUpper j) := by
  dsimp only
  have ht : Cycle63.Optimization.slotFloor ≤ z/M ∧ z/M ≤ Cycle63.Optimization.slotTop := by
    unfold Cycle63.Optimization.slotFloor Cycle63.Optimization.slotTop
    constructor
    · exact (le_div_iff₀ hM).mpr hz.1
    · exact (div_le_iff₀ hM).mpr hz.2
  obtain ⟨hj1,hj600,hl,hu⟩ := originalCell_mem ht
  have hb := cellUpper_bounds hj1 hj600
  have hzup : z ≤ cellUpper (originalCell (z/M))*M := (div_le_iff₀ hM).mp hu
  have hzlow : (cellUpper (originalCell (z/M))-Cycle63.Optimization.cellMesh)*M ≤ z :=
    (le_div_iff₀ hM).mp hl
  have hcoef : 0 ≤ (9/2:ℝ)-lambda := by linarith [lambda_bounds'.2]
  have hcoef' : 0 ≤ lambda-1 := by linarith [lambda_bounds'.1]
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
    (hz : z ≤ Cycle63.Optimization.slotTop*M) (hξ : ξ ≤ Cycle63.Physical.comparisonPadding*M) :
    M/4 + (M/2+ξ) + (9/2)*z ≤ M := by
  unfold Cycle63.Physical.comparisonPadding at hξ
  linarith

#print axioms originalCell_mem
#print axioms normalized_cell_bounds
end
end Cycle63.Moment
