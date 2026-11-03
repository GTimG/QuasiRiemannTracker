/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ValuedFieldTheory/LocalField/Padic/Cyclotomic/TotallyRamified/IntegralTranslate.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinRelation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Translation of the integral ring in the totally ramified cyclotomic extension

This file records that translating `ζ` by one preserves the explicit integral closure.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u

section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

local instance padicCyclotomicTotallyRamifiedIntegralTranslateAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedIntegralTranslateScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Translating the generator by one does not change the explicit
`ℤ_[p]`-algebra. -/
theorem padicCyclotomicTotallyRamified_adjoin_sub_one_eq_adjoin
    (ζ : L) :
    Algebra.adjoin ℤ_[p] ({ζ - 1} : Set L) =
      Algebra.adjoin ℤ_[p] ({ζ} : Set L) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Subalgebra.sub_mem _
      (Algebra.self_mem_adjoin_singleton ℤ_[p] ζ)
      (Subalgebra.one_mem _)
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simpa using Subalgebra.add_mem _
      (Algebra.self_mem_adjoin_singleton ℤ_[p] (ζ - 1))
      (Subalgebra.one_mem _)

end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
