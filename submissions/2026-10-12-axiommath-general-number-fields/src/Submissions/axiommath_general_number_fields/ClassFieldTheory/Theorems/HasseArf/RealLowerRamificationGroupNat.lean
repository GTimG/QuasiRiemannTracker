/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/RealLowerRamificationGroupNat.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HasseArf.RealLowerRamificationGroup
public import Submissions.axiommath_general_number_fields.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-! # Real lower groups at natural indices -/

namespace ClassFieldTheory

universe u v

/-- The real lower group at a natural index is the original lower group. -/
theorem realLowerRamificationGroup_nat
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    realLowerRamificationGroup K A (n : ℝ) = lowerRamificationGroup K A n := by
  have hpow : (Int.ceil ((n : ℝ) + 1)).toNat = n + 1 :=
    RamificationTheory.HilbertRamification.Higher.realRamificationExponent_nat n
  apply Subgroup.ext
  intro σ
  change (∀ x : A,
      σ • x - x ∈ (IsLocalRing.maximalIdeal A) ^ (Int.ceil ((n : ℝ) + 1)).toNat) ↔
    (∀ x : A, σ • x - x ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1))
  rw [hpow]

end ClassFieldTheory
