/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HilbertSymbols/KummerAlgebraFinrank.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Rank of a Kummer algebra

The rank of `K[X] / (X ^ n - a)` is `n` regardless of whether the polynomial
is irreducible. This is distinct from the index of its norm subgroup.
-/

namespace ClassFieldTheory

universe u

/-- The Kummer algebra has the polynomial's degree as its dimension. -/
theorem kummerAlgebra_finrank
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    Module.finrank K (KummerAlgebra K n a) = (n : ℕ) := by
  let p : Polynomial K :=
    Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  change Module.finrank K (Polynomial K ⧸ Ideal.span {p}) = (n : ℕ)
  rw [finrank_quotient_span_eq_natDegree]
  exact Polynomial.natDegree_X_pow_sub_C

end ClassFieldTheory
