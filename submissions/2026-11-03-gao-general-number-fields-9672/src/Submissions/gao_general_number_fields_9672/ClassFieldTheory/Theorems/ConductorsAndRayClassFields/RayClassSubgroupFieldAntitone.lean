/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassSubgroupFieldAntitone.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupEmbedding

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Inclusion of ray-class subgroup class fields

The fields are intermediate fields of one fixed separable closure, so the
conclusion is literal inclusion rather than merely an abstract embedding.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- For one modulus, a larger ray-class subgroup gives a smaller class
field inside the fixed separable closure.  This holds for any choices of
Frobenius-normalized realizations. -/
theorem rayClassSubgroupField_antitone
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K)
    {H J : Subgroup (RayClassGroup m)} (hHJ : H ≤ J)
    (RH : RayClassSubgroupRealization K m H)
    (RJ : RayClassSubgroupRealization K m J) :
    RJ.extension.1 ≤ RH.extension.1 := by
  obtain ⟨f, _⟩ :=
    exists_rayClassSubgroupEmbedding_artinNaturality K m hHJ RH RJ
  let σ : RJ.extension →ₐ[K] SeparableClosure K :=
    (IntermediateField.val RH.extension.1).comp f
  have hσ : σ.fieldRange = RJ.extension.1 :=
    AlgHom.fieldRange_of_normal σ
  rw [← hσ]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  exact (f y).property

end ClassFieldTheory

end
