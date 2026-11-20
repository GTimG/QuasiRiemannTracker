/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/DedekindZetaNonvanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.TwelfthRootNonvanishing
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Nonvanishing.Descent.AbelianZeroTransfer
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthCyclotomicExtension

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem dedekindZeta_ne_zero (K : Type) [Field K] [NumberField K] :
    ∃ f : Complex → Complex,
      DifferentiableOn Complex f (({1} : Set Complex)ᶜ) ∧
      (∀ s : Complex, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : Complex, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by
  obtain ⟨hGal, hcomm, hTC, hζ⟩ := cyclotomic12_context K
  obtain ⟨fF, hfF, hagF, hnzF⟩ :=
    mu12_continuation_ne_zero (CyclotomicField 12 K) hTC ⟨hζ.choose, hζ.choose_spec.1⟩
  exact dedekindZeta_zeroFree_of_abelian_extension K (CyclotomicField 12 K)
    hcomm (31 / 32) fF hfF hagF hnzF

end DedekindZetaZeroFree.Quantitative
