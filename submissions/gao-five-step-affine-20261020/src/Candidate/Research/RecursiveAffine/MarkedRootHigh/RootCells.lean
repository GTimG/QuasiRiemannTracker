import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootReserve
import Candidate.Cycle63.Moment.CellGeometry
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Cycle153.MarkedRootPrice
noncomputable section
open Cycle63.Optimization

/-- The original total slot width selects the amplifier once: the first cell whose upper edge is
at least the width. -/
abbrev originalCell := Cycle63.Moment.originalCell
abbrev cellUpper := Cycle63.Arithmetic.cellUpper
def cellCount : ℕ := 638098
def g (b : ℝ) : ℝ := B-1+(6*Cycle63.Optimization.slotPrice-lambda)*b
theorem one_le_cellCount : 1≤cellCount := by norm_num [cellCount]
theorem cellCount_mul : (cellCount:ℝ)*cellMesh=top-slotFloor := by norm_num [cellCount,cellMesh,allowanceUnit,top,slotFloor]

theorem cellUpper_bounds {j : ℕ} (hj1 : 1≤j) (hjn : j≤cellCount) :
    firstCellTop≤cellUpper j ∧ cellUpper j≤top := by
  have h1 : (1:ℝ)≤j := by exact_mod_cast hj1
  have hn : (j:ℝ)≤cellCount := by exact_mod_cast hjn
  have hm:=cellMesh_pos
  have hc:=cellCount_mul
  unfold cellUpper Cycle63.Arithmetic.cellUpper firstCellTop
  constructor <;> nlinarith

theorem g_pos {b : ℝ} (hb : b∈Set.Icc bottom top) : 0<g b := by
  have hl:=lambda_bounds;have hB:=B_bounds
  have hcell : b∈Set.Icc (3400001/100000000:ℝ) (2019049/50000000) := by
    convert hb using 1 <;> norm_num [bottom,top,firstCellTop,slotFloor,cellMesh,allowanceUnit]
  simp only [g,slotPrice,betaBound]
  rat_pos [hcell,hl,hB]

theorem amp_pos {b : ℝ} (hb : b∈Set.Icc bottom top) : 0<amp b := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hB:=B_bounds
  have hcell : b∈Set.Icc (3400001/100000000:ℝ) (2019049/50000000) := by
    convert hb using 1 <;> norm_num [bottom,top,firstCellTop,slotFloor,cellMesh,allowanceUnit]
  simp only [amp]
  priced_channels
  rat_pos [hcell,hk,hi,hq,hl,hB]


theorem originalCell_mem {t : ℝ}
    (ht : Cycle63.Optimization.slotFloor ≤ t ∧ t ≤ top) :
    1 ≤ originalCell t ∧ originalCell t ≤ cellCount ∧
      cellUpper (originalCell t) - Cycle63.Optimization.cellMesh ≤ t ∧
      t ≤ cellUpper (originalCell t) := by
  have hm := Cycle63.Optimization.cellMesh_pos
  have hcm := cellCount_mul
  have hx : 0 ≤ (t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh :=
    div_nonneg (by linarith [ht.1]) hm.le
  have hxm : (t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh*Cycle63.Optimization.cellMesh =
      t - Cycle63.Optimization.slotFloor := div_mul_cancel₀ _ hm.ne'
  have hc : ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊ ≤
      cellCount := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hm]
    linarith [ht.2]
  have hle := Nat.le_ceil ((t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh)
  have hlt := Nat.ceil_lt_add_one hx
  have hi : 1 ≤ originalCell t := le_max_left _ _
  have hi' : originalCell t ≤ cellCount :=
    max_le one_le_cellCount hc
  refine ⟨hi, hi', ?_, ?_⟩
  · by_cases hc1 : ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊ ≤ 1
    · simp only [originalCell,Cycle63.Moment.originalCell, max_eq_left hc1, cellUpper,Cycle63.Arithmetic.cellUpper, Nat.cast_one]
      linarith [ht.1]
    · simp only [originalCell,Cycle63.Moment.originalCell, max_eq_right (by omega :
        1 ≤ ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊), cellUpper,Cycle63.Arithmetic.cellUpper]
      nlinarith [mul_lt_mul_of_pos_right hlt hm]
  · have hcast : (⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊ : ℝ) ≤
        (originalCell t : ℝ) := by
      exact_mod_cast (le_max_right 1 ⌈(t - Cycle63.Optimization.slotFloor)/Cycle63.Optimization.cellMesh⌉₊)
    unfold cellUpper Cycle63.Arithmetic.cellUpper
    nlinarith [mul_le_mul_of_nonneg_right (hle.trans hcast) hm.le]

theorem normalized_cell_bounds {M n₁ n₂ z : ℝ} (hM : 0 < M)
    (hz : Cycle63.Optimization.slotFloor*M ≤ z ∧ z ≤ top*M)
    (haffine : n₁+n₂+lambda*z ≤ B*M) :
    let j := originalCell (z/M)
    1 ≤ j ∧ j ≤ cellCount ∧
      max (n₁+n₂+(6*Cycle63.Optimization.slotPrice)*z-M) 0 ≤ M*g (cellUpper j) ∧
      n₁+n₂+z ≤ M*totalA (cellUpper j) ∧
      0 < M*amp (cellUpper j) := by
  dsimp only
  have ht : Cycle63.Optimization.slotFloor ≤ z/M ∧ z/M ≤ top := by
    constructor
    · exact (le_div_iff₀ hM).mpr hz.1
    · exact (div_le_iff₀ hM).mpr hz.2
  obtain ⟨hj1,hj600,hl,hu⟩ := originalCell_mem ht
  have hb := cellUpper_bounds hj1 hj600
  have hzup : z ≤ cellUpper (originalCell (z/M))*M := (div_le_iff₀ hM).mp hu
  have hzlow : (cellUpper (originalCell (z/M))-Cycle63.Optimization.cellMesh)*M ≤ z :=
    (le_div_iff₀ hM).mp hl
  have hcoef : 0 ≤ 6*Cycle63.Optimization.slotPrice-lambda := by
    linarith [lambda_bounds.2, Cycle63.Optimization.slotPrice_mem.1]
  have hcoef' : 0 ≤ lambda-1 := by linarith [lambda_bounds.1]
  have hdef := mul_le_mul_of_nonneg_left hzup hcoef
  have htotal := mul_le_mul_of_nonneg_left hzlow hcoef'
  have hg := g_pos hb
  have hamp := amp_pos hb
  refine ⟨hj1,hj600, max_le ?_ (mul_pos hM hg).le, ?_, mul_pos hM hamp⟩
  · unfold g
    nlinarith
  · unfold totalA
    nlinarith

end
end Cycle153.MarkedRootPrice

#print axioms Cycle153.MarkedRootPrice.originalCell_mem
#print axioms Cycle153.MarkedRootPrice.normalized_cell_bounds
