/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassSubgroupRealizationEq.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupFieldAntitone

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Uniqueness of a ray-class subgroup field inside the fixed closure

The class field is independent of the Frobenius-normalized realization as an
actual intermediate field, not just up to abstract isomorphism.  This does
not assert uniqueness of the embedding or of the Artin map.
-/

namespace ClassFieldTheory

/-- Two realizations for the same modulus and subgroup have the same
intermediate field in the chosen separable closure. -/
theorem rayClassSubgroupRealizations_eq
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R₁ R₂ : RayClassSubgroupRealization K m H) :
    R₁.extension.1 = R₂.extension.1 := by
  apply le_antisymm
  · exact rayClassSubgroupField_antitone K m (le_refl H) R₂ R₁
  · exact rayClassSubgroupField_antitone K m (le_refl H) R₁ R₂

end ClassFieldTheory
