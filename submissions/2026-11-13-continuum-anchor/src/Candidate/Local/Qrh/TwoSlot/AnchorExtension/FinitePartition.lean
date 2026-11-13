/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorExtension

/-- A finite sequence of adjacent intervals covers the interval between its
last and first endpoints. The endpoints need not form an equally spaced grid. -/
theorem finite_partition_cover (R : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hlo : R n ≤ r) (hhi : r ≤ R 0) :
    ∃ j < n, R (j + 1) ≤ r ∧ r ≤ R j := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : r ≤ R n
    · exact ⟨n, Nat.lt_succ_self n, hlo, h⟩
    · have hn' : 0 < n := by
        by_contra hn'
        have : n = 0 := by omega
        subst n
        exact h hhi
      obtain ⟨j, hj, hjlo, hjhi⟩ := ih hn' (le_of_lt (lt_of_not_ge h))
      exact ⟨j, Nat.lt_succ_of_lt hj, hjlo, hjhi⟩

end Qrh.TwoSlot.AnchorExtension
