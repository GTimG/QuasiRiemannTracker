/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/RayClassSubgroupFieldAntitone.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Subgroup order and chosen ray class fields

The selected field of a larger ray-class subgroup is contained in that of
a smaller subgroup, as actual subfields of the fixed separable closure.
-/

open scoped NumberField Classical

noncomputable section

namespace ClassFieldTheory

/-- For one modulus, inclusion of ray-class subgroups reverses inclusion of
their selected class fields inside the fixed separable closure. -/
theorem chosenRayClassSubgroupSubfield_antitone
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K)
    {H J : Subgroup (RayClassGroup m)} (hHJ : H ≤ J) :
    GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupSubfield
        (K := K) (GlobalClassFieldComparison.rayClassModulusToOriginal K m)
        (J.map (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).toMonoidHom) ≤
      GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupSubfield
        (K := K) (GlobalClassFieldComparison.rayClassModulusToOriginal K m)
        (H.map (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).toMonoidHom) := by
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m
  have hmap : H.map e.toMonoidHom ≤ J.map e.toMonoidHom :=
    Subgroup.map_mono hHJ
  have hfixed :
      GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupFixedField
          (K := K) m' (J.map e.toMonoidHom) ≤
        GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupFixedField
          (K := K) m' (H.map e.toMonoidHom) := by
    exact IntermediateField.fixedField_le (Subgroup.map_mono hmap)
  exact
    IntermediateField.map_mono
      (GlobalClassFieldTheory.GlobalClassFields.rayClassFieldEmbedding K m')
      hfixed

end ClassFieldTheory

end
