/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum
open Set

/-- A strict downward slope reserve dominates the curve on a finite stage
whenever the derivative varies by less than that reserve. This is the
local finite-step estimate used before choosing the common stage mesh. -/
theorem finite_step_dominates {W D : ℝ → ℝ} {a R gamma : ℝ}
    (ha : a ≤ R)
    (hW : ∀t∈Icc a R, HasDerivAt W (D t) t)
    (hvariation : ∀t∈Icc a R, D R-gamma ≤ D t) :
    ∀r∈Icc a R, W r ≤ W R+(D R-gamma)*(r-R) := by
  let G : ℝ → ℝ := fun t => W t-(W R+(D R-gamma)*(t-R))
  have hg (t:ℝ) (ht:t∈Icc a R) : HasDerivAt G (D t-(D R-gamma)) t := by
    convert
      (hW t ht).sub ((hasDerivAt_const t (W R)).add
        (((hasDerivAt_id t).sub_const R).const_mul (D R-gamma))) using 1 <;>
      simp [G]
    funext x
    rfl
  have hmono : MonotoneOn G (Icc a R) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a R)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hg t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact sub_nonneg.mpr (hvariation t (interior_subset ht))
  intro r hr
  have hh := hmono hr ⟨ha,le_rfl⟩ hr.2
  dsimp [G] at hh
  nlinarith

end Qrh.TwoSlot.AnchorContinuum
#print axioms Qrh.TwoSlot.AnchorContinuum.finite_step_dominates
