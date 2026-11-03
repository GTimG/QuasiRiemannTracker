/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassIdealNormImageEqArtinKer.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicIdealArtinKernelComparison
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicIdealNormQuotientComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# The ideal norm subgroup is the Artin kernel

This is the ideal-theoretic norm-kernel form of finite abelian reciprocity.
The ideal norms are norms of fractional ideals prime to the modulus; the
principal ray ideals are absorbed by the ray quotient.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- For finite abelian reciprocity data, the image of genuine ideal norms
in the ideal ray class group equals the normalized Artin kernel. -/
theorem rayClassIdealNormImage_eq_artinKer
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    rayClassIdealNormImage K L D.modulus = D.artin.ker := by
  let m := GlobalClassFieldComparison.rayClassModulusToOriginal K D.modulus
  have hsource :=
    GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinKernel_eq_idealNormSubgroup_of_finiteExtension
      (K := K) (L := L) m
      (GlobalClassFieldComparison.finiteAbelianReciprocity_modulus_isDefining K L D)
  have hquot :=
    GlobalClassFieldComparison.publicIdealNormImage_comap_rayQuotient
      K L D.modulus
  apply Subgroup.ext
  intro x
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo D.modulus) x
  have hnorm :
      (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo D.modulus) I) ∈
        rayClassIdealNormImage K L D.modulus ↔
      I ∈ RayClass.idealNormSubgroup (K := K) (L := L) m := by
    exact Subgroup.ext_iff.mp hquot I
  rw [hnorm, ← hsource]
  exact (GlobalClassFieldComparison.publicArtinKer_iff_idealArtinKernel
    K L D I).symm

end ClassFieldTheory

end
