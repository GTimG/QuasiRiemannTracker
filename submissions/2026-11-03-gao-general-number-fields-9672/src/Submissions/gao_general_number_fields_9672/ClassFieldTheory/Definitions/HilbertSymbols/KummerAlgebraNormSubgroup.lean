/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/KummerAlgebraNormSubgroup.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
public import Mathlib.RingTheory.Norm.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Norm subgroup of a Kummer algebra

This is the image of the determinant norm on units of `K[X] / (X^n - a)`.
The algebra need not be a field, so this subgroup is defined without any
irreducibility assumption on the polynomial.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- The unit-norm image of the possibly reducible Kummer algebra. -/
def kummerAlgebraNormSubgroup
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) : Subgroup Kˣ :=
  (Units.map (Algebra.norm K : KummerAlgebra K n a →* K)).range

end ClassFieldTheory

end
