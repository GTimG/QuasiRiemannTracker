import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelHigh
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.LocalMoment.UnmarkedDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The payment of the depth-two HIGH rows: the exponent of a pair of a first-level LOW child and a second-level HIGH
label is at most minus the margin of the two-level ledger, plus the losses. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Physical
noncomputable section
open Cycle63.Optimization

/-! The exponent of a pair is the sum of the two compensated outside coordinates and the two missing radicals, the
density times the row-norm exponent of the pair, the bin times the volume exponent of the grandchild, the price of the
fixed deletion and the energy scale of the child. Each level pays its reserve `m (1 - ρ) - δ A - a (5 - 6ρ)` by the
first-level saving; the row norm of the pair exceeds the second-level coordinate by the log norm of the child
multiplier, which the scale identity of the child converts into the first-level coordinate. What remains is the
reserve `highTwoAt δ b` of the two-level ledger. -/

/-- The density exponent of the two-level ledger is the unmarked density of the count. -/
theorem density_eq_unmarkedDensity (δ : ℝ) : density δ = OAI.SevenEighths.LocalMoment.unmarkedDensity δ := rfl

/-- In every HIGH bin of the second step the density exponent lies in `[0, 1]`, the amplifier cost is nonnegative and
the bin lies above the first junction. -/
theorem second_high_bin_bounds {δ : ℝ} (hδ : secondJunction ≤ δ ∧ δ ≤ 3/4) :
    0 ≤ density δ ∧ density δ ≤ 1 ∧ 0 ≤ amplifierCost δ ∧ firstJunction ≤ δ := by
  have hq := secondJunction_mem
  have hq0 := firstJunction_mem
  have hden : 0 < 3*(5 - 2*δ) := by linarith [hδ.2]
  have hup : 10*δ/(3*(5 - 2*δ)) ≤ 1 := by
    rw [div_le_one hden]
    linarith [hδ.2]
  have hlow : 1/6 ≤ 10*δ/(3*(5 - 2*δ)) := by
    rw [le_div_iff₀ hden]
    linarith [hδ.1, hq.1]
  unfold amplifierCost density
  exact ⟨by linarith, by linarith, by linarith, by linarith [hq0.2, hq.1, hδ.1]⟩

/-- The exponent of a pair of a first-level LOW child and a second-level HIGH label is at most `-highTwoMargin` plus
the losses. Premises: the two first-level payments with their reserves written out and their common-rate savings
`γ₁, γ₂ ≥ 0`, the row-norm bound `q ≤ X2₂ + Lv` of the pair (`Lv` the log norm of the child multiplier), the scale
identity `m₂ + Lv ≤ X2₁ + κ` of the child, its volume after deleting slots of total width `deleted`, the target
`fixedDeletion b ≤ target ≤ deleted` of the deletion, and the cell bounds of the two-level ledger, with the amplifier
of the second level at most `secondAmp b` up to the padding `ω`. The losses are the two first-level losses, the
scale constant `κ`, the volume padding, the mesh and the excess of the deletion price over the first junction, and
the padding of the amplifier. -/
theorem depth_two_pair_exponent_bound {δ b : ℝ} (hδ : secondJunction ≤ δ ∧ δ ≤ 3/4)
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop)
    {X0₁ X1₁ X2₁ X3₁ X0₂ X1₂ X2₂ X3₂ m₁ A₁ a₁ m₂ A₂ a₂ small₁ small₂ γ₁ γ₂ : ℝ}
    {q Lv κ deleted target mesh pad price ω : ℝ}
    (h₁ : X0₁ + X1₁ + density δ*X2₁ + δ*X3₁ ≤
      small₁ - (m₁*(1 - density δ) - δ*A₁ - a₁*amplifierCost δ) - γ₁)
    (h₂ : X0₂ + X1₂ + density δ*X2₂ + δ*X3₂ ≤
      small₂ - (m₂*(1 - density δ) - δ*A₂ - a₂*amplifierCost δ) - γ₂)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hq : q ≤ X2₂ + Lv) (hscale : m₂ + Lv ≤ X2₁ + κ)
    (hvol : A₂ ≤ X3₁ - deleted + pad) (hdel : fixedDeletion b ≤ target) (htarget : target ≤ deleted)
    (hm₁ : 1 ≤ m₁) (hA₁ : A₁ ≤ twoLevelTotalA b) (ha₁ : a₁ ≤ firstAmp b) (ha₂ : a₂ ≤ secondAmp b + ω) :
    X0₁ + X0₂ + X1₁ + X1₂ + density δ*q + δ*X3₂ + price*(target + mesh) + m₂ ≤
      -highTwoMargin + small₁ + small₂ + density δ*κ + δ*pad + price*mesh + (price - firstJunction)*target +
        amplifierCost δ*ω := by
  obtain ⟨hρ0, hρ1, hh, hq0⟩ := second_high_bin_bounds hδ
  have hcert := highTwo_certificate hδ hb
  unfold highTwoAt at hcert
  have hδ0 : 0 ≤ δ := by linarith [hδ.1, secondJunction_mem.1]
  have e₁ := mul_le_mul_of_nonneg_left hq hρ0
  have e₂ := mul_le_mul_of_nonneg_left hscale hρ0
  have e₃ := mul_le_mul_of_nonneg_left hvol hδ0
  have e₄ := mul_le_mul_of_nonneg_left htarget hδ0
  have e₅ := mul_le_mul_of_nonneg_left hdel (sub_nonneg.mpr hq0)
  have e₆ := mul_le_mul_of_nonneg_left hm₁ (sub_nonneg.mpr hρ1)
  have e₇ := mul_le_mul_of_nonneg_left hA₁ hδ0
  have e₈ := mul_le_mul_of_nonneg_left ha₁ hh
  have e₉ := mul_le_mul_of_nonneg_left ha₂ hh
  linarith

end
end Cycle63.Physical

end Record1252270103Bootstrap.PR67
