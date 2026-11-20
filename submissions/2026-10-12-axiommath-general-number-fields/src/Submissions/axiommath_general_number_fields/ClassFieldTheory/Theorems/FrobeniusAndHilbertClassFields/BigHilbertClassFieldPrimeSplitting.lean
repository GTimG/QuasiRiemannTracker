/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/BigHilbertClassFieldPrimeSplitting.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusEqOneIffSplitsCompletely
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldArtinEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Prime splitting in the big Hilbert class field

A finite prime splits completely in the big Hilbert class field precisely
when its narrow ideal class is trivial.  Real-place ramification does not
affect this finite-prime criterion.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- A finite prime splits completely in the big Hilbert class field exactly
when its narrow ray class is trivial. -/
theorem finitePrime_splitsCompletelyInBigHilbertClassField_iff
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePrimeSplitsCompletely K E v ↔
      narrowRayClassOfFinitePrime v = 1 := by
  obtain ⟨artin, hartin⟩ := bigHilbertClassField_artinEquiv K E hE
  have hunram : Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := hE.1 v
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 E) v.asIdeal
  let : Q.LiesOver v.asIdeal := hQover
  let w : HeightOneSpectrum (𝓞 E) :=
    ⟨Q, hQmax.isPrime,
      Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw : w.asIdeal.LiesOver v.asIdeal := hQover
  constructor
  · intro hsplit
    apply artin.injective
    rw [map_one, hartin v w hw]
    exact (arithmeticFrobeniusAt_eq_one_iff_splitsCompletely
      v w hw hunram).2 hsplit
  · intro hclass
    apply (arithmeticFrobeniusAt_eq_one_iff_splitsCompletely
      v w hw hunram).1
    rw [← hartin v w hw, hclass, map_one]

end ClassFieldTheory

end
