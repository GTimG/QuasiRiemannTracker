/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Mellin/StrongPairContinuation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem mellinStrongPairContinuation (P : WeakFEPair ℂ) (hk : P.k = 1)
    (hP : IsStrongFEPair P) :
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ s : ℂ, HasMellin P.f s (P.Λ s)) ∧
    (∀ s : ℂ, HasMellin P.g s (P.symm.Λ s)) ∧
    (∀ s : ℂ, P.Λ s = P.ε * P.symm.Λ (1 - s)) := by
  refine ⟨hP.differentiable_Λ, hP.symm.differentiable_Λ, hP.hasMellin,
    hP.symm.hasMellin, ?_⟩
  intro s
  have h := P.functional_equation (1 - s)
  rw [hk, Complex.ofReal_one, sub_sub_cancel, smul_eq_mul] at h
  exact h

end DedekindZetaZeroFree.Hecke
