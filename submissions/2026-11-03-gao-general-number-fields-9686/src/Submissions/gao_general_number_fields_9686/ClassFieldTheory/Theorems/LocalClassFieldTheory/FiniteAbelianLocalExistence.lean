/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistence.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalExistenceOrderIso

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite abelian local existence

This module states the existence half of finite abelian local class field
theory.  Both sides of the correspondence are expressed directly with
Mathlib objects: intermediate fields of `SeparableClosure K` and subgroups
of `Kˣ`.  No implementation-specific class-formation object appears in the
statement.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- Every open finite-index subgroup of `Kˣ` is the norm subgroup of a
finite abelian subextension. -/
theorem finiteAbelianLocalExistence
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∀ H : OpenFiniteIndexSubgroup K,
      ∃ E : FiniteAbelianLocalExtension K,
        E.normSubgroup = H.1 := by
  obtain ⟨e, he⟩ := finiteAbelianLocalExistence_orderIso K
  intro H
  refine ⟨e.symm (OrderDual.toDual H), ?_⟩
  have h := he (e.symm (OrderDual.toDual H))
  rw [e.apply_symm_apply] at h
  exact h.symm

end ClassFieldTheory

end
