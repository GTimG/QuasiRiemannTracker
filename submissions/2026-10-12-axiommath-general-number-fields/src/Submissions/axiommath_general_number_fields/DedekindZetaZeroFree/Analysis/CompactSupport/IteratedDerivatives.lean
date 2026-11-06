/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/CompactSupport/IteratedDerivatives.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem contDiff_iteratedDeriv (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n h) := by
  rw [iteratedDeriv_eq_iterate]
  exact hh.iterate_deriv n

theorem hasCompactSupport_iteratedDeriv (h : ℝ → ℂ) (hh : HasCompactSupport h)
    (n : ℕ) : HasCompactSupport (iteratedDeriv n h) := by
  induction n with
  | zero => simpa using hh
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

end DedekindZetaZeroFree.LargeSieve.Vendor
