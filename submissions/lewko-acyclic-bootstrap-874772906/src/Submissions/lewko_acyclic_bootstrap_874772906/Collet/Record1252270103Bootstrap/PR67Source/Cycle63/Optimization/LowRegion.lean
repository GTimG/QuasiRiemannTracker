import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TopRow
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The region into which the LOW children of a step are deleted, and the amplifier that pays the deletion.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-! The LOW children of a step are deleted into a region `A + (6κ - 1) z ≤ I M` of states, given by its slot price
`κ` (`price`) and its intercept `I` (`intercept`). A child of a parent cell whose gap over the region is `g` and
whose amplifier is `a` overshoots the region by `g + 6 I a`, and deleting it costs `q/(6κ)` per unit of
overshoot at the junction `q`. -/

variable (price intercept : ℝ)

/-- Amplifier ratio of the LOW ledger at the bin split `q0`: the amplifier length per unit of gap over the
region, `q0/(6 (κ - q0 I))`, for which the LOW reserve is `alpha (1 - q0 I/κ)`. -/
def amplifierRatio (q0 : ℝ) : ℝ := q0/(6*(price - q0*intercept))

/-- Weight of the HIGH branch in the coupled plane. -/
def weight (q0 : ℝ) : ℝ := amplifierRatio price intercept q0 * (5 - 6*density q0)

/-- The LOW reserve `alpha (1 - q0 I/κ)` is what remains of the amplifier length `Ka g + alpha` after the LOW
slots of gap `g` over the region and the amplifier's width are paid at the rate `q0/(6 κ)`. -/
theorem low_reserve_cancel {q0 : ℝ} (hk : price ≠ 0) (hq : price - q0*intercept ≠ 0) (g alpha : ℝ) :
    (amplifierRatio price intercept q0*g + alpha)*(1 - q0*intercept/price) - (q0/(6*price))*g =
      alpha*(1 - q0*intercept/price) := by
  have key : amplifierRatio price intercept q0 * (1 - q0*intercept/price) = q0/(6*price) := by
    unfold amplifierRatio
    field_simp
  linear_combination g * key

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
