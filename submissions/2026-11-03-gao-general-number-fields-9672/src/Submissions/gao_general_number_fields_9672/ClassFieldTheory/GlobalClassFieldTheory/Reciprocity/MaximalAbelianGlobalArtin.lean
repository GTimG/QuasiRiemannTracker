/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/MaximalAbelianGlobalArtin.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinSurjectivity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Global Artin map for the maximal abelian extension

This module specializes the continuous infinite global Artin map to the
maximal abelian subextension of the separable closure.  It also exposes the
idele-representative evaluation and its finite Galois projections.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type) [Field K] [NumberField K]

/-- The continuous global Artin homomorphism from the idele class group to
the Galois group of the maximal abelian extension. -/
noncomputable def maximalAbelianGlobalArtin :
    IdeleClassGroup K →ₜ* Gal(maximalAbelianExtension K / K) :=
  infiniteGlobalIdeleClassArtinContinuousMonoidHom
    (K := K) (Ω := maximalAbelianExtension K)

/-- Evaluation of the maximal abelian global Artin map on an idele
representative recovers the infinite global Artin map. -/
@[simp]
theorem maximalAbelianGlobalArtin_mk (a : IdeleGroup K) :
    maximalAbelianGlobalArtin K
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) =
      infiniteGlobalArtinMonoidHom K (maximalAbelianExtension K) a :=
  infiniteGlobalIdeleClassArtinMonoidHom_mk
    (K := K) (Ω := maximalAbelianExtension K) a

/-- Projection of the maximal abelian global Artin map at an idele
representative to a finite Galois intermediate field agrees with the finite
global Artin map. -/
@[simp]
theorem maximalAbelianGlobalArtin_finiteProjection
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    letI : NumberField E := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (maximalAbelianGlobalArtin K
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a)) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  let : NumberField E := NumberField.of_module_finite K E
  rw [maximalAbelianGlobalArtin_mk]
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom
      K (maximalAbelianExtension K) a E

/-- The maximal abelian global Artin homomorphism is surjective. -/
theorem maximalAbelianGlobalArtin_surjective :
    Function.Surjective (maximalAbelianGlobalArtin K) :=
  infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective
    K (maximalAbelianExtension K)

end Reciprocity
end GlobalClassFieldTheory

end
