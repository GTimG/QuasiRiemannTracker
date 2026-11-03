/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/BigHilbertClassFieldNarrowRayRealization.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldArtinEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# The big Hilbert class field as a narrow ray class field

Its narrow-class Artin isomorphism and unramifiedness at finite primes give
a ray-class-field realization whose extension is the original field.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- A big Hilbert class field realizes the narrow ray class group, with
the same extension and arithmetic Frobenius normalization. -/
theorem bigHilbertClassField_hasNarrowRayRealization
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E) :
    ∃ R : RayClassFieldRealization K (narrowRayClassModulus K),
      R.extension = E := by
  classical
  obtain ⟨artin, hartin⟩ := bigHilbertClassField_artinEquiv K E hE
  let R : RayClassFieldRealization K (narrowRayClassModulus K) := {
    extension := E
    unramifiedOutsideModulus := by
      constructor
      · intro v _
        exact hE.1 v
      · intro v hv hnot
        have hmem : (⟨v, hv⟩ : RayClassRealPlace K) ∈
            (narrowRayClassModulus K).infinitePart :=
          Finset.mem_univ _
        exact (hnot hmem).elim
    artinEquiv := artin
    artin_frobenius := by
      intro v _ w hw
      change artin (narrowRayClassOfFinitePrime v) =
        arithmeticFrobeniusAt (K := K) w
      exact hartin v w hw }
  exact ⟨R, rfl⟩

end ClassFieldTheory

end
