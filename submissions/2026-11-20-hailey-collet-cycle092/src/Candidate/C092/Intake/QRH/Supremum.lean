/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# The supremum step in Appendix Q.4

These lemmas use the actual set of allowed zero real parts.  They do not assume
that its supremum is attained.  Analytic estimates for the manuscript's
L-function, and the boundedness/nonemptiness of its zero set, are not supplied
by this module.
-/

set_option autoImplicit false

namespace QRH.Cycle090

/-- Real parts of actual zeros that satisfy an explicit eligibility predicate.
The predicate can exclude poles and restrict the presentation or zero strip. -/
def zeroRealParts (L : ℂ → ℂ) (allowed : ℂ → Prop) : Set ℝ :=
  {a | ∃ z : ℂ, allowed z ∧ L z = 0 ∧ z.re = a}

/-- Appendix Q.4: an actual zero lies within `m / 2` of the supremum.
No member of the zero set is asserted to attain that supremum. -/
theorem actual_zero_near_supremum
    (L : ℂ → ℂ) (allowed : ℂ → Prop)
    (hne : (zeroRealParts L allowed).Nonempty)
    (hbdd : BddAbove (zeroRealParts L allowed))
    {m : ℝ} (hm : 0 < m) :
    ∃ z : ℂ, allowed z ∧ L z = 0 ∧
      sSup (zeroRealParts L allowed) - m / 2 < z.re ∧
      z.re ≤ sSup (zeroRealParts L allowed) := by
  have hlt : sSup (zeroRealParts L allowed) - m / 2 <
      sSup (zeroRealParts L allowed) := by linarith
  obtain ⟨a, ha, hza⟩ := exists_lt_of_lt_csSup hne hlt
  obtain ⟨z, hzallowed, hz, hreal⟩ := ha
  refine ⟨z, hzallowed, hz, ?_, ?_⟩
  · simpa only [hreal] using hza
  · exact le_csSup hbdd ⟨z, hzallowed, hz, rfl⟩

/-- The positive losses in Q.4 can be chosen for every strictly positive gap.
`a` is the lower boundary where the numerator is already known not to vanish. -/
theorem choose_mellin_losses {β t σ a : ℝ}
    (hgap : t < β) (hsigma : 0 < σ) (ha : a < t) :
    ∃ ω m : ℝ,
      0 < ω ∧ ω < (β - t) / 4 ∧ 0 < m ∧
      m < β - t - ω ∧ m < σ ∧ m < β - a := by
  have hquarter : 0 < (β - t) / 4 := by linarith
  obtain ⟨ω, hω0, hω⟩ := exists_between hquarter
  have hremaining : 0 < β - t - ω := by linarith
  have hfloor : 0 < β - a := by linarith
  have hmin : 0 < min (min (β - t - ω) σ) (β - a) :=
    lt_min (lt_min hremaining hsigma) hfloor
  obtain ⟨m, hm0, hm⟩ := exists_between hmin
  obtain ⟨hm₁, hm₂⟩ := lt_min_iff.mp hm
  obtain ⟨hm₃, hm₄⟩ := lt_min_iff.mp hm₁
  exact ⟨ω, m, hω0, hω, hm0, hm₃, hm₄, hm₂⟩

/-- A zero within `m / 2` of `β` is inside the continued half-plane and above
the numerator's nonvanishing boundary, provided the Q.4 loss constraints hold. -/
theorem near_supremum_in_continuation {β m a r : ℝ}
    (hm : 0 < m) (hma : m < β - a) (hr : β - m / 2 < r) :
    β - m < r ∧ a < r := by
  constructor <;> linarith

end QRH.Cycle090
