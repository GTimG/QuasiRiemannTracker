/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/CyclicNormConductor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Narrow finite conductors of cyclic class-norm subgroups

For a finite cyclic extension, the actual idele-class norm quotient has
order equal to the extension degree.  Substituting this norm-index
theorem into the narrow finite conductor ray-class factorization identifies
the ray class number at the exact narrow finite conductor as the product of the
residual norm-subgroup image order and the extension degree.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

/-- For a finite cyclic extension, the ray class number at the exact
narrow finite norm conductor is the order of the norm-subgroup image modulo
the conductor congruence subgroup times the extension degree. -/
theorem
    narrowFiniteConductorRayClassGroup_card_eq_normSubgroupImage_card_mul_extensionDegree :
    Nat.card
        (RayClass.RayClassGroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L)))) =
      Nat.card
          (Subgroup.map
            (QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup
                (RayClass.Modulus.narrowOfFinite
                  (ideleClassNormNarrowFiniteConductor
                    (K := K) (L := L)))))
            ((_root_.ideleClassNorm K L).range)) *
        Module.finrank K L := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      narrowFiniteConductorRayClassGroup_card_eq_normSubgroupImage_card_mul_normQuotient_card
        (K := K) (L := L)

/-- The degree of a finite cyclic extension divides the ray class
number at the exact narrow finite conductor of its idèle-class norm
subgroup. -/
theorem cyclicExtensionDegree_dvd_narrowFiniteConductorRayClassGroup_card :
    Module.finrank K L ∣
      Nat.card
        (RayClass.RayClassGroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L)))) := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      ideleClassNormQuotient_card_dvd_narrowFiniteConductorRayClassGroup_card
        (K := K) (L := L)

end GlobalClassFields
end GlobalClassFieldTheory

end
