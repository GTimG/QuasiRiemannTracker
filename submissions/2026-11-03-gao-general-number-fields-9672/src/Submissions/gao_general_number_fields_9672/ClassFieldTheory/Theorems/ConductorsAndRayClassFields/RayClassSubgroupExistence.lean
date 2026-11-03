/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassSubgroupExistence.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Existence of the class field of a ray-class subgroup

Every subgroup of an ideal-theoretic ray class group is the kernel of the
Frobenius-normalized Artin map of a finite abelian extension.  The statement
uses ideal classes; the proof transports the existing idelic reciprocity
construction to that interface.
-/

open scoped Classical NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every ray-class subgroup has a finite abelian class-field realization. -/
theorem rayClassSubgroup_existence
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) :
    Nonempty (RayClassSubgroupRealization K m H) := by
  exact GlobalClassFieldComparison.rayClassSubgroup_existence K m H

end ClassFieldTheory

end
