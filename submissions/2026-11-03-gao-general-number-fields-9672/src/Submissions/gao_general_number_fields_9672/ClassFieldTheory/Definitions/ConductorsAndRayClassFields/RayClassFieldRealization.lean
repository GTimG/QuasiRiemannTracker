/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassFieldRealization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Ray class fields
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- A finite abelian extension realizing the ray class group through a
Frobenius-normalized Artin isomorphism. -/
structure RayClassFieldRealization
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) where
  /-- The ray class field. -/
  extension : FiniteAbelianExtension K
  /-- The extension is unramified away from the modulus. -/
  unramifiedOutsideModulus :
    IsUnramifiedOutsideModulus K extension m
  /-- The Artin isomorphism for the ray class field. -/
  artinEquiv : RayClassGroup m ≃* (extension ≃ₐ[K] extension)
  /-- A prime class maps to arithmetic Frobenius. -/
  artin_frobenius :
    ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ m.finitePart.support)
      (w : HeightOneSpectrum (𝓞 extension)),
      w.asIdeal.LiesOver v.asIdeal →
        artinEquiv (rayClassOfFinitePrime m v hv) =
          arithmeticFrobeniusAt (K := K) w

end ClassFieldTheory
