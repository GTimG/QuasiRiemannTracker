/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/FiniteAbelianLocalReciprocityIndex.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Index formula in finite abelian local reciprocity

The index of the norm subgroup equals the degree of the finite abelian local
extension.  This is the numerical form of the reciprocity isomorphism.
-/

namespace ClassFieldTheory

/-- The norm-subgroup index is the degree of the extension. -/
theorem fieldNormSubgroup_index_eq_finrank
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (fieldNormSubgroup K L).index = Module.finrank K L := by
  exact LocalCFT.fieldNormSubgroup_index_eq_finrank K L

end ClassFieldTheory
