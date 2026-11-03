/-
2026-11-03 refinement by Zhongpai Gao (https://github.com/Gaozhongpai).
The following header records the PR #114 source provenance at 09afbb4ce6570c1615d58509dc197fc9f0956b7d.
This file now contains the native parameter refinement at
829193272c1eaf223bb7228fbfb9003f414808e9; local imports are relocated under Submissions.gao_general_number_fields_9686.
Original declaration namespaces and all source attribution are retained.
Native compilation and tracker admission remain pending; see Candidate.Provenance.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/Quantitative/DedekindZetaNonvanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.TwelfthRootNonvanishing
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Nonvanishing.Descent.AbelianZeroTransfer
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthCyclotomicExtension

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem dedekindZeta_ne_zero (K : Type) [Field K] [NumberField K] :
    ∃ f : Complex → Complex,
      DifferentiableOn Complex f (({1} : Set Complex)ᶜ) ∧
      (∀ s : Complex, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : Complex, 4843 / 5000 < s.re → s ≠ 1 → f s ≠ 0 := by
  obtain ⟨hGal, hcomm, hTC, hζ⟩ := cyclotomic12_context K
  obtain ⟨fF, hfF, hagF, hnzF⟩ :=
    mu12_continuation_ne_zero (CyclotomicField 12 K) hTC ⟨hζ.choose, hζ.choose_spec.1⟩
  exact dedekindZeta_zeroFree_of_abelian_extension K (CyclotomicField 12 K)
    hcomm (4843 / 5000) fF hfF hagF hnzF

end DedekindZetaZeroFree.Quantitative
