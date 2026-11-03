/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Dedekind/HolomorphicContinuation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Dedekind.ReciprocalGammaFactor
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Analysis.EntireDivisionAtZero
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Dedekind.MixedThetaMellinModel
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Nonvanishing.Mellin.WeakFunctionalEquationUncompletion

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

theorem zetaContinuation (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s := by

  obtain ⟨P, hk, hP⟩ := zeta_mixedThetaModel K

  obtain ⟨u, hu, hqu⟩ := entire_division_at_zero (zetaGammaReciprocal K)
    (zetaGammaReciprocal_differentiable K) (zetaGammaReciprocal_zero K)
  have hq : Differentiable ℂ (zetaGammaReciprocal K) := zetaGammaReciprocal_differentiable K

  refine ⟨fun s => zetaGammaReciprocal K s * P.Λ₀ s - u s * P.f₀
      - zetaGammaReciprocal K s * (P.ε / (1 - s)) * P.g₀, ?_, ?_⟩
  · exact (weakFE_uncompletion P hk (zetaGammaReciprocal K) u hq hu hqu).1
  · intro s hs
    have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
    rw [(weakFE_uncompletion P hk (zetaGammaReciprocal K) u hq hu hqu).2 s hs0 hs1]

    have hPm : P.Λ s = zetaGammaFactor K s * NumberField.dedekindZeta K s := by
      have h1 := (P.hasMellin (s := s) (by rw [hk]; exact hs)).2
      have h2 := (hP s hs).2
      exact h1.symm.trans h2
    rw [hPm, ← mul_assoc, zetaGammaReciprocal_mul_factor K s hs, one_mul]

end DedekindZetaZeroFree.AbelianQuotient
