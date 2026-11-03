/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/BigHilbertClassFieldArtinEquiv.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldMathlibArtin

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Artin isomorphism for the big Hilbert class field

The narrow ideal class group is isomorphic to the Galois group of the big
Hilbert class field.  The displayed compatibility with arithmetic Frobenius
fixes the Artin normalization of the isomorphism.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- The narrow class group acts through the Frobenius-normalized Artin
isomorphism on a big Hilbert class field. -/
theorem bigHilbertClassField_artinEquiv
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E) :
    ∃ artin : RayClassGroup (narrowRayClassModulus K) ≃*
        (E ≃ₐ[K] E),
      ∀ (v : HeightOneSpectrum (𝓞 K))
        (w : HeightOneSpectrum (𝓞 E)),
        w.asIdeal.LiesOver v.asIdeal →
          artin (narrowRayClassOfFinitePrime v) =
            arithmeticFrobeniusAt (K := K) w := by
  let g :=
    GlobalClassFieldComparison.arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_of_isBig E hE
  let artin : RayClassGroup (narrowRayClassModulus K) ≃* (E ≃ₐ[K] E) :=
    (GlobalClassFieldComparison.narrowRayClassGroupEquivNarrowClassGroup K).trans g.symm
  refine ⟨artin, ?_⟩
  intro v w hw
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    hE.1 v w.asIdeal inferInstance hw
  apply g.injective
  calc
    g (artin (narrowRayClassOfFinitePrime v)) =
        QuotientGroup.mk' (RayClass.narrowDenominator (K := K))
          (IdeleGroup.finitePrimeIdele v) := by
      rw [show g (artin (narrowRayClassOfFinitePrime v)) =
          GlobalClassFieldComparison.narrowRayClassGroupEquivNarrowClassGroup K
            (narrowRayClassOfFinitePrime v) from by
        simp only [artin, MulEquiv.trans_apply, g.apply_symm_apply]]
      exact GlobalClassFieldComparison.narrowRayClassGroupEquivNarrowClassGroup_prime v
    _ = g (arithmeticFrobeniusAt (K := K) w) := by
      rw [← GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := E) v w hw hunram]
      exact (GlobalClassFieldComparison.arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroup_prime
        E hE v).symm

end ClassFieldTheory

end
