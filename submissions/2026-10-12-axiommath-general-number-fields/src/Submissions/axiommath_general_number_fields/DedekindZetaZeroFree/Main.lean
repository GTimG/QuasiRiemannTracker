/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Main.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.DedekindZetaNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree

theorem dedekindZeta_ne_zero
    (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by
  exact DedekindZetaZeroFree.Quantitative.dedekindZeta_ne_zero K

end DedekindZetaZeroFree
