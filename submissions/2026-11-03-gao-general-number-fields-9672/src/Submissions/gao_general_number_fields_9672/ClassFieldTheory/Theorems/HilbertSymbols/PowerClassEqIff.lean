/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HilbertSymbols/PowerClassEqIff.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Equality of power classes

Two representatives have the same power class precisely when their ratio
is an `n`-th power.
-/

namespace ClassFieldTheory

universe u

/-- Two elements represent the same power class exactly when their ratio is
an `n`-th power. -/
theorem powerClass_eq_iff
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) :
    powerClass K n a = powerClass K n b ↔
      a / b ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  exact QuotientGroup.eq_iff_div_mem

end ClassFieldTheory
