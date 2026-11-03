/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/NormTheorems/CyclicHasseNormTheorem.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.NormTheorems.IsEverywhereLocalNorm
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.FieldTheory.Galois.Basic
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.MathlibNormInterface

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# The cyclic Hasse norm theorem

This module states the local-to-global norm principle for a finite cyclic
Galois extension `L / K` of number fields.  For a unit `x` of `K`, the
conclusion identifies membership in the global field-norm subgroup with the
condition of being a norm after base change to every finite and infinite
completion of `K`.
-/

open scoped NumberField

namespace ClassFieldTheory

/-- For a finite cyclic number-field extension, a unit is a global norm if
and only if it is a norm at every completion. -/
theorem cyclicHasseNormTheorem
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (x : Kˣ) :
    IsFieldNorm K L x ↔ IsEverywhereLocalNorm K L x := by
  exact GlobalClassFieldTheory.ClassFieldAxiom.cyclicHasseNormTheorem K L x

end ClassFieldTheory
