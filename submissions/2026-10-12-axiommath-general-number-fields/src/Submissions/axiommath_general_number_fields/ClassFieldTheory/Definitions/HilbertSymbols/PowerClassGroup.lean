/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/PowerClassGroup.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Multiplicative power-class groups
-/

namespace ClassFieldTheory

universe u

/-- The multiplicative group of a field modulo its `n`-th powers. -/
def PowerClassGroup (K : Type u) [Field K] (n : ℕ+) : Type u :=
  Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range

instance instCommGroupPowerClassGroup
    (K : Type u) [Field K] (n : ℕ+) : CommGroup (PowerClassGroup K n) := by
  unfold PowerClassGroup
  infer_instance

end ClassFieldTheory
