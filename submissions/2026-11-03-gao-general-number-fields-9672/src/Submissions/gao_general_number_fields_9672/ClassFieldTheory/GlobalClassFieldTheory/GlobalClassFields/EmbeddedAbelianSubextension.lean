/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/EmbeddedAbelianSubextension.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality
public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Embedded finite abelian subextensions

An embedding of an actual finite abelian extension into the rational
separable closure determines a finite abelian subextension of the fixing
subgroup of the embedded base field. This file also allows that base fixing
subgroup to be replaced by a propositionally equal selected subgroup, as is
needed by concrete class-field realizations.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open Reciprocity

/-- An actual finite abelian extension embedded in the rational separable
closure, represented as a finite abelian subextension of a selected base
subgroup equal to the fixing subgroup of the embedded base field. -/
noncomputable def numberFieldEmbeddedAbelianSubextension
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (j : E →ₐ[ℚ] SeparableClosure ℚ)
    (B : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hbase : numberFieldEmbeddedBaseSubgroup K E j = B) :
    FiniteAbelianSubextension B := by
  subst B
  exact
    { toFiniteGaloisExtension :=
        numberFieldEmbeddedFiniteGaloisSubextension K E j
      commutative := by
        let e :
            (numberFieldEmbeddedFiniteGaloisSubextension K E j).extensionQuotient ≃*
              Gal(E / K) := by
          exact
            numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
              K E j
        exact
          { is_comm.comm := fun x y => by
              apply e.injective
              simpa only [map_mul] using
                (inferInstance :
                  IsMulCommutative
                    (Gal(E / K))).is_comm.comm
                  (e x) (e y) } }

/-- The top subgroup of the embedded abelian subextension is the fixing
subgroup of the embedded top field. -/
@[simp]
theorem numberFieldEmbeddedAbelianSubextension_field
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (j : E →ₐ[ℚ] SeparableClosure ℚ)
    (B : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hbase : numberFieldEmbeddedBaseSubgroup K E j = B) :
    (numberFieldEmbeddedAbelianSubextension K E j B hbase).field =
      numberFieldEmbeddedTopSubgroup K E j := by
  subst B
  rfl

end GlobalClassFields
end GlobalClassFieldTheory

end
