/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite upper width cells, including a one-point width interval. -/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section

def upperWidthCell (cross cap δ s : ℝ) : ℝ :=
  min cap (cross + (Nat.ceil ((min cap (max cross s)-cross)/δ) : ℝ)*δ)

def widthCellGrid (cross cap δ : ℝ) : Finset ℝ :=
  (Finset.range (Nat.ceil ((cap-cross)/δ)+1)).image
    (fun i : ℕ => min cap (cross+(i:ℝ)*δ))

theorem upperWidthCell_mem_grid (cross cap δ s : ℝ) (hδ : 0<δ) :
    upperWidthCell cross cap δ s ∈ widthCellGrid cross cap δ := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨Nat.ceil ((min cap (max cross s)-cross)/δ),?_,rfl⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Nat.ceil_mono
    (div_le_div_of_nonneg_right (sub_le_sub_right (min_le_left _ _) _) hδ.le))

theorem upperWidthCell_finite_range (cross cap δ : ℝ) (hδ : 0<δ) :
    (Set.range (upperWidthCell cross cap δ)).Finite := by
  apply (widthCellGrid cross cap δ).finite_toSet.subset
  rintro _ ⟨s,rfl⟩
  exact upperWidthCell_mem_grid cross cap δ s hδ

theorem upperWidthCell_bounds (cross cap δ s : ℝ) (hδ : 0<δ)
    (hlo : cross≤s) (hhi : s≤cap) :
    s≤upperWidthCell cross cap δ s ∧ upperWidthCell cross cap δ s≤cap ∧
      0≤upperWidthCell cross cap δ s-s ∧ upperWidthCell cross cap δ s-s≤δ := by
  have hceil := Nat.le_ceil ((s-cross)/δ)
  have hceil' := Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.mpr hlo) hδ.le)
  have hdiv : (s-cross)/δ*δ=s-cross := div_mul_cancel₀ _ hδ.ne'
  have hlow := mul_le_mul_of_nonneg_right hceil hδ.le
  have hupp := mul_lt_mul_of_pos_right hceil' hδ
  rw [hdiv] at hlow
  rw [add_mul,hdiv,one_mul] at hupp
  simp only [upperWidthCell,max_eq_right hlo,min_eq_right hhi]
  have hmin : s≤min cap (cross+(Nat.ceil ((s-cross)/δ):ℝ)*δ) :=
    le_min hhi (by linarith)
  refine ⟨hmin,min_le_left _ _,sub_nonneg.mpr hmin,?_⟩
  have hm := min_le_right cap (cross+(Nat.ceil ((s-cross)/δ):ℝ)*δ)
  linarith

theorem upperWidthCell_degenerate (cross δ s : ℝ) (_hδ : 0<δ) :
    upperWidthCell cross cross δ s=cross := by
  simp [upperWidthCell]

/-- The only enlargement of the clipped plain budget is the stated λδ. -/
theorem upperWidthCell_plain_budget (B lam cross cap δ s : ℝ) (hδ : 0<δ)
    (hlam : 0≤lam) (hlo : cross≤s) (hhi : s≤cap) :
    B-lam*s≤(B-lam*upperWidthCell cross cap δ s)+lam*δ := by
  have h := mul_le_mul_of_nonneg_left
    (upperWidthCell_bounds cross cap δ s hδ hlo hhi).2.2.2 hlam
  nlinarith

/-- A positive rounding scale selected from a genuine uniform scalar margin,
an independently specified fee allowance, and all fixed linear loss factors. -/
def widthRoundingScale (margin allowance loss : ℝ) : ℝ :=
  min 1 (min allowance (margin/2))/(1+|loss|)

theorem widthRoundingScale_spec (margin allowance loss : ℝ)
    (hm : 0<margin) (ha : 0<allowance) :
    0<widthRoundingScale margin allowance loss ∧
    widthRoundingScale margin allowance loss≤1 ∧
    |loss| *widthRoundingScale margin allowance loss≤allowance ∧
    2*(|loss| *widthRoundingScale margin allowance loss)≤margin := by
  let e := min 1 (min allowance (margin/2))
  have he : 0<e := lt_min (by norm_num) (lt_min ha (by linarith))
  have hd : 0<1+|loss| := by positivity
  have hδ : 0<e/(1+|loss|) := div_pos he hd
  have hprod : (e/(1+|loss|))*(1+|loss|)=e := div_mul_cancel₀ _ hd.ne'
  have hunit : e≤1 := min_le_left _ _
  have hallow : e≤allowance := (min_le_right _ _).trans (min_le_left _ _)
  have hmargin : e≤margin/2 := (min_le_right _ _).trans (min_le_right _ _)
  change 0<e/(1+|loss|) ∧ e/(1+|loss|)≤1 ∧
    |loss| *(e/(1+|loss|))≤allowance ∧ 2*(|loss| *(e/(1+|loss|)))≤margin
  refine ⟨hδ,?_,?_,?_⟩ <;> nlinarith [abs_nonneg loss]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.upperWidthCell_finite_range
#print axioms QRH.Record1252270103Low.upperWidthCell_bounds
#print axioms QRH.Record1252270103Low.upperWidthCell_plain_budget
#print axioms QRH.Record1252270103Low.widthRoundingScale_spec
