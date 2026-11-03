/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/KummerAlgebra.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.FieldTheory.KummerExtension

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Canonical Kummer algebras
-/

namespace ClassFieldTheory

universe u

/-- The Kummer algebra `K[X] / (X^n - a)`.  It remains canonical when the
polynomial is reducible, so no root in a chosen closure is required. -/
abbrev KummerAlgebra
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :=
  AdjoinRoot (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K))

end ClassFieldTheory
