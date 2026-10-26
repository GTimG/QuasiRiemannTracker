import Mathlib
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The arithmetic facts of a first-level LOW child in the branch of the second step, in units of its width, from the
absolute lengths of the child. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section

/-- The facts that the second step asks of a first-level LOW child of the cell `b` of its parent: in units of the
width `M₁` of the child (itself in units of the width of the parent) its plain lengths are `n₁, n₂` and its slot length
is `ζ`. The child overshoots the old region of slot price `κ`, and by at most the overshoot `childOverB` of the
zero-extraction child of the cell plus `ω`; its total length leaves the reserve `childResB` of the zero-extraction
child up to `ω`; its plain lengths differ by at most `6 κ ζ + s`; it lies in the region of slope `lam₂` and intercept
`I` up to `3 ω`; and its slot length, in units of the parent, is at most the slot length `b - fixedDelB` of the cell
after the fixed deletion. -/
structure ChildBranchFacts (κ lam₂ I b fixedDelB childOverB childResB M₁ n₁ n₂ ζ s ω : ℝ) : Prop where
  width : 2/5 ≤ M₁ ∧ M₁ ≤ 1
  slack : s ≤ 1/100
  omega : 0 ≤ ω ∧ ω ≤ 1/1000000
  slot_nonneg : 0 ≤ ζ
  slot_cell : ζ * M₁ ≤ b - fixedDelB
  overshoot_pos : 0 < n₁ + n₂ + 6 * κ * ζ - 1
  overshoot_le : (n₁ + n₂ + 6 * κ * ζ - 1) * M₁ ≤ childOverB + ω
  reserve : childResB ≤ (1 - (n₁ + n₂ + ζ)) * M₁ + ω
  balance : |n₁ - n₂| ≤ 6 * κ * ζ + s
  region : n₁ + n₂ + lam₂ * ζ ≤ I + 3 * ω

/-- A child of the second step's branch has the facts of the second step in units of its width `W`. The data are the
absolute lengths `x₁, x₂, z'` of the child, the width `u` of the parent, the nominal width `ν` of the child and its
width `W` widened by the width slack, the padding, the cell values of the parent and the extraction credit: `v` is the
width reduction of the child, `Red` its reduction that is credited to the length, and `mt` the mesh of the cell
times the slope less one. -/
theorem child_branch_facts {κ lam₂ I b d0 gN ampN totN cO cR u ν W x₁ x₂ z' rem del pad omega ξ δR v Red mt : ℝ}
    (hu : 0 < u) (hW2 : 2/5 * u ≤ W) (hWu : W ≤ u) (hνW : ν ≤ W) (hκ : 0 ≤ κ) (hlam₂ : 1 ≤ lam₂) (hI0 : 0 ≤ I)
    (hI : I ≤ 1) (hpad : 0 ≤ pad) (homega : 0 ≤ omega) (hmt : 0 ≤ mt)
    (hz' : 0 ≤ z')
    (hover : cO = gN + 6 * ampN - 6 * κ * d0) (hres : cR = 1 - 6 * ampN - totN + d0)
    (hreg : totN - d0 + (lam₂ - 1) * (b - d0) = I * (1 - 6 * ampN) + mt)
    (hdel : del = u * d0) (hrem : rem ≤ u * b) (hz'le : z' ≤ rem - del)
    (hv : 0 ≤ v) (hRed : 0 ≤ Red) (hνdef : ν = u - v - 6 * (u * ampN) - omega)
    (hN4 : x₁ + x₂ + 6 * κ * rem - ν ≤ u * gN + 6 * (u * ampN) + pad - Red)
    (hN4u : x₁ + x₂ + rem ≤ u * totN + pad - (v + Red))
    (hnotO : W < x₁ + x₂ + 6 * κ * z')
    (hbal : |x₁ - x₂| ≤ 6 * κ * z' + (ξ + δR))
    (hsmall : ξ + δR ≤ 1/100 * (2/5 * u)) (hsmallω : pad + omega + u * mt ≤ 1/1000000 * u) :
    ChildBranchFacts κ lam₂ I b d0 cO cR (W / u) (x₁ / W) (x₂ / W) (z' / W) ((ξ + δR) / W)
      ((pad + omega) / u + mt) := by
  subst hdel
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hW2
  have hz'u : z' ≤ u * b - u * d0 := by linarith only [hz'le, hrem]
  have hωu : 0 ≤ (pad + omega) / u + mt := by positivity
  have hωeq : ((pad + omega) / u + mt) * u = pad + omega + u * mt := by field_simp
  have hrs : 0 ≤ pad + omega + u * mt := by positivity
  have hu0mt : 0 ≤ u * mt := mul_nonneg hu.le hmt
  refine ⟨⟨?_, ?_⟩, ?_, ⟨hωu, ?_⟩, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hu]; linarith
  · rw [div_le_one hu]; exact hWu
  · rw [div_le_iff₀ hW0]; linarith
  · have h : ((pad + omega) / u + mt) * u ≤ 1/1000000 * u := by rw [hωeq]; exact hsmallω
    exact le_of_mul_le_mul_right h hu
  · -- the slot length of the child in units of the parent
    show z' / W * (W / u) ≤ b - d0
    have : z' / W * (W / u) = z' / u := by field_simp
    rw [this, div_le_iff₀ hu]
    linarith only [hz'u]
  · -- the child overshoots the old region
    show 0 < x₁ / W + x₂ / W + 6 * κ * (z' / W) - 1
    have : x₁ / W + x₂ / W + 6 * κ * (z' / W) - 1 = (x₁ + x₂ + 6 * κ * z' - W) / W := by field_simp
    rw [this]
    exact div_pos (by linarith) hW0
  · -- the overshoot is at most that of the zero-extraction child
    show (x₁ / W + x₂ / W + 6 * κ * (z' / W) - 1) * (W / u) ≤ cO + ((pad + omega) / u + mt)
    have : (x₁ / W + x₂ / W + 6 * κ * (z' / W) - 1) * (W / u) = (x₁ + x₂ + 6 * κ * z' - W) / u := by
      field_simp
    rw [this, div_le_iff₀ hu]
    have h6 : 6 * κ * z' ≤ 6 * κ * (rem - u * d0) := mul_le_mul_of_nonneg_left hz'le (by positivity)
    have h7 : (cO + ((pad + omega) / u + mt)) * u = u * cO + (pad + omega + u * mt) := by
      rw [add_mul, hωeq, mul_comm]
    rw [h7, hover]
    linarith only [hN4, h6, hνW, hRed, homega, hu0mt]
  · -- the reserve of the zero-extraction child
    show cR ≤ (1 - (x₁ / W + x₂ / W + z' / W)) * (W / u) + ((pad + omega) / u + mt)
    have : (1 - (x₁ / W + x₂ / W + z' / W)) * (W / u) = (W - (x₁ + x₂ + z')) / u := by field_simp
    rw [this, hres, ← sub_nonneg]
    have : (W - (x₁ + x₂ + z')) / u + ((pad + omega) / u + mt) - (1 - 6 * ampN - totN + d0) =
        (W - (x₁ + x₂ + z') + (pad + omega + u * mt) - u * (1 - 6 * ampN - totN + d0)) / u := by
      field_simp
    rw [this]
    apply div_nonneg _ hu.le
    linarith only [hN4u, hz'le, hνW, hνdef, hRed, hv, hu0mt, hωeq]
  · -- the plain lengths are balanced
    show |x₁ / W - x₂ / W| ≤ 6 * κ * (z' / W) + (ξ + δR) / W
    have : |x₁ / W - x₂ / W| = |x₁ - x₂| / W := by
      rw [← sub_div, abs_div, abs_of_pos hW0]
    rw [this, div_le_iff₀ hW0]
    have : (6 * κ * (z' / W) + (ξ + δR) / W) * W = 6 * κ * z' + (ξ + δR) := by field_simp
    rw [this]; exact hbal
  · -- the child lies in the region of the second step
    show x₁ / W + x₂ / W + lam₂ * (z' / W) ≤ I + 3 * ((pad + omega) / u + mt)
    have hsplit : x₁ / W + x₂ / W + lam₂ * (z' / W) = (x₁ + x₂ + lam₂ * z') / W := by field_simp
    rw [hsplit, div_le_iff₀ hW0]
    have h4 : ((pad + omega) / u + mt) * (2/5 * u) ≤ ((pad + omega) / u + mt) * W :=
      mul_le_mul_of_nonneg_left hW2 hωu
    have h5 : ((pad + omega) / u + mt) * (2/5 * u) = 2/5 * (pad + omega + u * mt) := by
      calc ((pad + omega) / u + mt) * (2/5 * u) = 2/5 * (((pad + omega) / u + mt) * u) := by ring
        _ = 2/5 * (pad + omega + u * mt) := by rw [hωeq]
    have hz'' : (lam₂ - 1) * z' ≤ (lam₂ - 1) * (u * b - u * d0) :=
      mul_le_mul_of_nonneg_left hz'u (by linarith)
    have hIν : I * ν ≤ I * W := mul_le_mul_of_nonneg_left hνW hI0
    have hν' : I * ν = I * u - I * v - 6 * (I * (u * ampN)) - I * omega := by rw [hνdef]; ring
    have hregu : u * totN - u * d0 + (lam₂ - 1) * (u * b - u * d0) = I * (u * (1 - 6 * ampN)) + u * mt := by
      linear_combination u * hreg
    have hv1 : 0 ≤ (1 - I) * v := mul_nonneg (sub_nonneg.mpr hI) hv
    have hom1 : 0 ≤ (1 - I) * omega := mul_nonneg (sub_nonneg.mpr hI) homega
    have hexp : (I + 3 * ((pad + omega) / u + mt)) * W = I * W + 3 * (((pad + omega) / u + mt) * W) := by ring
    rw [hexp]
    linarith only [hN4u, hz'le, hz'', hregu, hIν, hν', h4, h5, hv1, hom1, hrs, hRed]

/-- A state that is not reflected into the old region has plain lengths that differ by at most `6 κ z` plus the slack
and the margin of the test: the capacity of the state exceeds the width by at most the margin `δR`, neither plain
factor, reflected with the slack `ξ`, leaves the state in the old region with the margin, and the margin is at most
half the width. -/
theorem balance_of_not_reflection {x₁ x₂ z W δR ξ κ : ℝ} (hz : 0 ≤ z)
    (hκ : 0 ≤ κ) (hξ : 0 < ξ) (hW : 2 * δR ≤ W)
    (hcap : x₁ + x₂ + 6 * κ * z ≤ W + δR)
    (hn₁ : ¬ (max 0 (W - x₂ + ξ) + x₁ + 6 * κ * z + δR ≤ W))
    (hn₂ : ¬ (max 0 (W - x₁ + ξ) + x₂ + 6 * κ * z + δR ≤ W)) :
    |x₁ - x₂| ≤ 6 * κ * z + (ξ + δR) := by
  have hκz : 0 ≤ 6 * κ * z := by positivity
  push Not at hn₁ hn₂
  rw [abs_le]
  constructor
  · -- x₂ - x₁ is small
    rcases le_total 0 (W - x₂ + ξ) with h | h
    · rw [max_eq_right h] at hn₁
      linarith
    · rw [max_eq_left h] at hn₁
      exfalso
      linarith
  · rcases le_total 0 (W - x₁ + ξ) with h | h
    · rw [max_eq_right h] at hn₂
      linarith
    · rw [max_eq_left h] at hn₂
      exfalso
      linarith

/-- The overshoot of a child over the old region, in units of the parent, is at most that of the zero-extraction child
of the cell plus the padding and the frequency loss, with no term of the mesh of the cell: it follows from the capacity
of the extraction alone. -/
theorem child_overshoot_nomesh {κ cO gN ampN d0 u ν W x₁ x₂ z' rem del pad omega Red : ℝ}
    (hu : 0 < u) (hW0 : 0 < W) (hκ : 0 ≤ κ) (hover : cO = gN + 6 * ampN - 6 * κ * d0) (hdel : del = u * d0)
    (hz'le : z' ≤ rem - del) (hνW : ν ≤ W) (hRed : 0 ≤ Red) (homega : 0 ≤ omega)
    (hN4 : x₁ + x₂ + 6 * κ * rem - ν ≤ u * gN + 6 * (u * ampN) + pad - Red) :
    (x₁ / W + x₂ / W + 6 * κ * (z' / W) - 1) * (W / u) ≤ cO + (pad + omega) / u := by
  have h1 : (x₁ / W + x₂ / W + 6 * κ * (z' / W) - 1) * (W / u) = (x₁ + x₂ + 6 * κ * z' - W) / u := by
    field_simp
  rw [h1, div_le_iff₀ hu]
  have h6 : 6 * κ * z' ≤ 6 * κ * (rem - u * d0) := by
    subst hdel
    exact mul_le_mul_of_nonneg_left hz'le (by positivity)
  have h7 : (cO + (pad + omega) / u) * u = u * cO + (pad + omega) := by
    field_simp
  rw [h7, hover]
  linarith only [hN4, h6, hνW, hRed, homega]

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
