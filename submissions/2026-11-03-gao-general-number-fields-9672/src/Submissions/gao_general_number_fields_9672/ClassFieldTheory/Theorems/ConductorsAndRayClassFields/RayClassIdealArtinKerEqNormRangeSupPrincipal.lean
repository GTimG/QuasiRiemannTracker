/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassIdealArtinKerEqNormRangeSupPrincipal.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealNormImageEqArtinKer

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Ideal Artin kernel before passage to ray classes

The kernel in prime-to-modulus ideals is the product of the genuine ideal
norm image and the principal ray-ideal subgroup.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- Before passing to ray classes, the Artin kernel is the product of the
genuine ideal-norm subgroup and the principal ray-ideal subgroup. -/
theorem rayClassIdealArtinKer_eq_normRange_sup_principal
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    (D.artin.comp
      (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo D.modulus))).ker =
      (rayClassPrimeToIdealNorm K L D.modulus).range ⊔
        rayPrincipalIdealSubgroupInPrimeTo D.modulus := by
  let q : rayClassPrimeToIdeals D.modulus →* RayClassGroup D.modulus :=
    QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo D.modulus)
  let N := (rayClassPrimeToIdealNorm K L D.modulus).range
  change (D.artin.comp q).ker = N ⊔
    rayPrincipalIdealSubgroupInPrimeTo D.modulus
  calc
    (D.artin.comp q).ker = D.artin.ker.comap q := by
      exact (MonoidHom.comap_ker D.artin q).symm
    _ = (rayClassIdealNormImage K L D.modulus).comap q := by
      rw [rayClassIdealNormImage_eq_artinKer K L D]
    _ = (N.map q).comap q := by
      rw [← MonoidHom.range_comp]
      rfl
    _ = N ⊔ rayPrincipalIdealSubgroupInPrimeTo D.modulus := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

end ClassFieldTheory

end
