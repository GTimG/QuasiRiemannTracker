/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldOrdinaryRayRealization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldArtinEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# The small Hilbert class field as an ordinary ray class field

Its ordinary-class Artin isomorphism and everywhere-unramifiedness give a
ray-class-field realization whose extension is the original field.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- A small Hilbert class field realizes the ordinary ray class group, with
the same extension and arithmetic Frobenius normalization. -/
theorem smallHilbertClassField_hasOrdinaryRayRealization
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    ∃ R : RayClassFieldRealization K (ordinaryRayClassModulus K),
      R.extension = E := by
  obtain ⟨artin, hartin⟩ := smallHilbertClassField_artinEquiv K E hE
  let R : RayClassFieldRealization K (ordinaryRayClassModulus K) := {
    extension := E
    unramifiedOutsideModulus := by
      constructor
      · intro v _
        exact hE.1.1 v
      · intro _ _ _ w _
        exact hE.1.2.isUnramified w
    artinEquiv := artin
    artin_frobenius := by
      intro v _ w hw
      change artin (ordinaryRayClassOfFinitePrime v) =
        arithmeticFrobeniusAt (K := K) w
      exact hartin v w hw }
  exact ⟨R, rfl⟩

end ClassFieldTheory

end
