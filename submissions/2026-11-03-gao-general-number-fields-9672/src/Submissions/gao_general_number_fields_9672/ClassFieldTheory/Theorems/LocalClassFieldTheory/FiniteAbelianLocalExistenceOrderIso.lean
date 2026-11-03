/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalExistenceOrderIso.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkLocalClassification
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Hom.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Order classification in finite abelian local existence

This module states the classification form of local existence for a
nonarchimedean local field `K`.  Finite abelian intermediate fields of
`SeparableClosure K` are ordered by field inclusion, whereas open
finite-index subgroups of `Kˣ` are ordered contravariantly.  The statement
also records that the order isomorphism sends each extension to its actual
field-norm subgroup.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- Finite abelian local extensions correspond contravariantly to open
finite-index norm subgroups. -/
theorem finiteAbelianLocalExistence_orderIso
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
  ∃ e : FiniteAbelianLocalExtension K ≃o
        (OpenFiniteIndexSubgroup K)ᵒᵈ,
      ∀ E : FiniteAbelianLocalExtension K,
        (OrderDual.ofDual (e E)).1 = E.normSubgroup := by
  exact ⟨LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso K,
    LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply K⟩

end ClassFieldTheory

end
