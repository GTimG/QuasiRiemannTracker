/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/FractionalIdealNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNormExponentMap
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Relative norm of nonzero fractional ideals

The norm sends a finite-prime factor upstairs to the prime below it, with
exponent multiplied by the inertia degree. Prime factorization extends this
rule to a multiplicative map on all nonzero fractional ideals.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The relative norm of nonzero fractional ideals of number fields,
defined by its inertia-degree-weighted action on prime exponents. -/
def fractionalIdealNorm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    NumberFieldFractionalIdealGroup L →*
      NumberFieldFractionalIdealGroup K :=
  (NumberFieldFractionalIdealGroup.factorizationEquiv
      (K := K)).toMonoidHom.comp
    ((fractionalIdealNormExponentMap K L).toMultiplicative.comp
      (NumberFieldFractionalIdealGroup.factorizationEquiv
        (K := L)).symm.toMonoidHom)

end ClassFieldTheory

end
