/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/AlgEquivTopology.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Local continuity for transport under a number-field equivalence

The finite-completion map used by `adeleCongr` is continuous. This is the
local continuity input for transporting the restricted-product topology.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- Field-isomorphism transport is continuous on each finite completion. -/
theorem finitePlaceAdicCompletionCongrHom_continuous
    (e : K ≃ₐ[ℚ] M) (W : HeightOneSpectrum (𝓞 M)) :
    Continuous (finitePlaceAdicCompletionCongrHom e W) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  unfold finitePlaceAdicCompletionCongrHom
  exact finitePlaceAdicCompletionMap_continuous K M _ _

end
