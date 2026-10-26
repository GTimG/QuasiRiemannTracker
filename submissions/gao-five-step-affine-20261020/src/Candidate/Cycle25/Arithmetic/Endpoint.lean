import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Exact arithmetic for T1 of the selected Cycle25 proof packet.
The endpoint is an algebraic real, specified by its polynomial and isolating interval.
These declarations make no assertion about Hecke or Dirichlet L-functions. -/

namespace Cycle25.Arithmetic

def quartic (x : ℝ) : ℝ := 927*x^4 - 3135*x^3 + 2433*x^2 + 275*x - 100
noncomputable def rootLo : ℝ := 16712007850680 / 100000000000000
noncomputable def rootHi : ℝ := 16712007850682 / 100000000000000

theorem rootLo_lt_rootHi : rootLo < rootHi := by norm_num [rootLo, rootHi]
theorem quartic_rootLo_neg : quartic rootLo < 0 := by norm_num [quartic, rootLo]
theorem quartic_rootHi_pos : 0 < quartic rootHi := by norm_num [quartic, rootHi]

theorem quartic_continuous : Continuous quartic := by unfold quartic; fun_prop

theorem exists_isolated_root : ∃ x : ℝ, rootLo < x ∧ x < rootHi ∧ quartic x = 0 := by
  have h := intermediate_value_Icc (le_of_lt rootLo_lt_rootHi)
    quartic_continuous.continuousOn
  obtain ⟨x, hx, hpx⟩ := h (show (0:ℝ) ∈ Set.Icc (quartic rootLo) (quartic rootHi) from
    ⟨le_of_lt quartic_rootLo_neg, le_of_lt quartic_rootHi_pos⟩)
  refine ⟨x, ?_, ?_, hpx⟩
  · exact lt_of_le_of_ne hx.1 (by intro he; subst x; linarith [quartic_rootLo_neg])
  · exact lt_of_le_of_ne hx.2 (by intro he; subst x; linarith [quartic_rootHi_pos])

noncomputable def ell0 : ℝ := Classical.choose exists_isolated_root

noncomputable def b0 : ℝ := 11/12 - ell0/4

end Cycle25.Arithmetic
