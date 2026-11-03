/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/ArithmeticFrobeniusAt.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Frobenius

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Arithmetic Frobenius at a finite prime
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Mathlib's chosen arithmetic Frobenius lift at a finite prime of the
extension field.  At a ramified prime such a lift need not be unique. -/
def arithmeticFrobeniusAt
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (w : HeightOneSpectrum (𝓞 L)) : L ≃ₐ[K] L :=
  arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal

end ClassFieldTheory

end
