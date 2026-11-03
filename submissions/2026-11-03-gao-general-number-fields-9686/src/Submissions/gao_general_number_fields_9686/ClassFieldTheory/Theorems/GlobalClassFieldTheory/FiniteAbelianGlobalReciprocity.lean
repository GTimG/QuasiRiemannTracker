/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/FiniteAbelianGlobalReciprocity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibGlobalReciprocity
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite abelian global reciprocity

For a finite abelian extension `L/K`, global reciprocity supplies a modulus
and a surjective Artin map from its ray class group to `Gal(L/K)`.  The
extension is unramified away from that modulus, and prime classes are sent to
Mathlib's arithmetic Frobenius elements.

The statement is ideal-theoretic; its proof transports the existing idelic
reciprocity construction through the ray class comparison.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- A finite abelian extension admits a Frobenius-normalized finite Artin map
through a ray class group. -/
theorem finiteAbelianGlobalReciprocity
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] :
    Nonempty (FiniteAbelianReciprocityData K L) := by
  let m := GlobalClassFieldComparison.normConductorRayClassModulus K L
  let hram : IsUnramifiedOutsideModulus K L m :=
    GlobalClassFieldComparison.normConductorRayClassModulus_unramifiedOutside K L
  refine ⟨{
    modulus := m
    unramifiedOutsideModulus := hram
    artin := GlobalClassFieldComparison.normConductorArtin K L
    artin_surjective := GlobalClassFieldComparison.normConductorArtin_surjective K L
    artin_frobenius := ?_
  }⟩
  intro v hv w hw
  calc
    GlobalClassFieldComparison.normConductorArtin K L (rayClassOfFinitePrime m v hv) =
        GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v :=
      GlobalClassFieldComparison.normConductorArtin_prime K L v hv
    _ = arithmeticFrobeniusAt (K := K) w :=
      GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
        (K := K) (L := L) v w hw (hram.1 v hv w.asIdeal inferInstance hw)

end ClassFieldTheory

end
