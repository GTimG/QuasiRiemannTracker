/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/GlobalClassFieldTheory/FiniteAbelianReciprocityData.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite abelian global reciprocity data

The interface is ideal-theoretic: a ray-class Artin map is normalized by
arithmetic Frobenius away from its modulus.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- Finite abelian global-reciprocity data in ideal-theoretic form. -/
structure FiniteAbelianReciprocityData
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] where
  /-- A modulus through which the finite Artin map factors. -/
  modulus : RayClassModulus K
  /-- The extension is unramified away from the modulus. -/
  unramifiedOutsideModulus : IsUnramifiedOutsideModulus K L modulus
  /-- The finite Artin map on the ray class group. -/
  artin : RayClassGroup modulus →* (L ≃ₐ[K] L)
  /-- The finite Artin map is onto. -/
  artin_surjective : Function.Surjective artin
  /-- A prime class maps to arithmetic Frobenius. -/
  artin_frobenius :
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ modulus.finitePart.support)
      (w : HeightOneSpectrum (𝓞 L)),
      w.asIdeal.LiesOver v.asIdeal →
        artin (rayClassOfFinitePrime modulus v hv) =
          arithmeticFrobeniusAt (K := K) w

end ClassFieldTheory
