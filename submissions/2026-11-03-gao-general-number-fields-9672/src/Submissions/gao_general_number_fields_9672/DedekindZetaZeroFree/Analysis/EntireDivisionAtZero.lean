/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/EntireDivisionAtZero.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

theorem entire_division_at_zero (q : ℂ → ℂ) (hq : Differentiable ℂ q) (hq0 : q 0 = 0) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s : ℂ, q s = s * u s := by
  refine ⟨dslope q 0, ?_, ?_⟩
  · rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).mpr
      hq.differentiableOn
  · intro s
    have h := sub_smul_dslope_of_zero hq0 s
    simpa using h.symm

end DedekindZetaZeroFree.AbelianQuotient
