/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/UnboundedOperators/FormalAdjointClosability.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section

namespace DedekindZetaZeroFree

theorem formalAdjoint_gradient_closable
    {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : H →ₗ.[ℂ] V) (δ : V →ₗ.[ℂ] H)
    (hδ : Dense (δ.domain : Set V)) (hformal : D.IsFormalAdjoint δ) :
    D ≤ δ.adjoint ∧ D.IsClosable ∧ D.closure.IsClosed := by
  have hle : D ≤ δ.adjoint := hformal.symm.le_adjoint hδ
  have hcl : D.IsClosable := (LinearPMap.adjoint_isClosed hδ).isClosable.leIsClosable hle
  exact ⟨hle, hcl, hcl.closure_isClosed⟩

end DedekindZetaZeroFree
