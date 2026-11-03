/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/ExistsUniqueAbelianConductor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsAbelianConductor
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.IsAbelianConductorUnique
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Unique existence of the abelian conductor

Existence of a least ray-class-field modulus and uniqueness of any modulus
with the same universal property combine into a unique-existence statement.
-/

namespace ClassFieldTheory

/-- The conductor of a finite abelian extension of number fields exists
uniquely. -/
theorem existsUnique_abelianConductor
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃! c : RayClassModulus K, IsAbelianConductor K L c := by
  obtain ⟨c, hc⟩ := exists_abelianConductor K L
  exact ⟨c, hc, fun d hd => hd.unique hc⟩

end ClassFieldTheory
