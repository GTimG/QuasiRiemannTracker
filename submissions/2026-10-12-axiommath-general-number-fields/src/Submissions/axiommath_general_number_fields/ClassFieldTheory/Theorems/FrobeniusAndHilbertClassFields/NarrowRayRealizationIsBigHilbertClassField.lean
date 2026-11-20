/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/NarrowRayRealizationIsBigHilbertClassField.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsRayArtinModulusProjection
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldExists
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldNarrowRayRealization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# A narrow ray realization is a big Hilbert class field

The Frobenius-normalized realization of the narrow ray class group is
maximal among finite abelian extensions unramified at finite places.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- Every realization of the narrow ray class group is a big Hilbert class
field, including its maximality property. -/
theorem narrowRayRealization_isBigHilbertClassField
    (K : Type) [Field K] [NumberField K]
    (R : RayClassFieldRealization K (narrowRayClassModulus K)) :
    IsBigHilbertClassField R.extension := by
  obtain ⟨E, hE⟩ := exists_bigHilbertClassField K
  obtain ⟨S, hS⟩ := bigHilbertClassField_hasNarrowRayRealization K E hE
  subst E
  obtain ⟨f, _⟩ :=
    exists_rayArtin_modulusProjection
      (le_refl (narrowRayClassModulus K)) S R
  constructor
  · intro v
    exact R.unramifiedOutsideModulus.1 v (by simp [narrowRayClassModulus])
  · intro F hF
    obtain ⟨g⟩ := hE.2 F hF
    exact ⟨f.comp g⟩

end ClassFieldTheory

end
