/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/LocalClassFieldTheory/FiniteAbelianLocalExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite abelian local extensions
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- A finite abelian extension of `K` inside Mathlib's chosen separable
closure.  The inherited order is field inclusion. -/
abbrev FiniteAbelianLocalExtension
    (K : Type u) [Field K] :=
  { E : IntermediateField K (SeparableClosure K) //
      FiniteDimensional K E ∧ IsAbelianGalois K E }

namespace FiniteAbelianLocalExtension

variable {K : Type u} [Field K]

/-- The packaged intermediate field is finite-dimensional over the base. -/
instance finiteDimensional (E : FiniteAbelianLocalExtension K) :
    FiniteDimensional K E.1 :=
  E.2.1

/-- The packaged intermediate field is abelian Galois over the base. -/
instance isAbelianGalois (E : FiniteAbelianLocalExtension K) :
    IsAbelianGalois K E.1 :=
  E.2.2

/-- The norm subgroup belonging to a packaged finite abelian extension. -/
def normSubgroup (E : FiniteAbelianLocalExtension K) : Subgroup Kˣ :=
  fieldNormSubgroup K E.1

end FiniteAbelianLocalExtension

end ClassFieldTheory

end
