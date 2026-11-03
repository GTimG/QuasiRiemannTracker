/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Dedekind/AbelianContinuation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Dedekind.EntireAbelianQuotient

@[expose] public section

namespace DedekindZetaZeroFree

theorem dedekindZeta_continuation
    (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s := by

  obtain ⟨fK, _fL, _g, hfK, _hfL, _hg, hagK, _hagL, _hquot⟩ :=
    DedekindZetaZeroFree.dedekindAbelianQuotient K K (fun σ τ => Subsingleton.elim (σ * τ) (τ * σ))
  exact ⟨fK, hfK, hagK⟩

end DedekindZetaZeroFree
