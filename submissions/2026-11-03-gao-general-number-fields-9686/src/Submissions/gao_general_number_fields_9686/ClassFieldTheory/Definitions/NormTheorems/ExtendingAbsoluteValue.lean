/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/NormTheorems/ExtendingAbsoluteValue.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.UniformSpace.AbsoluteValue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Absolute values above a fixed absolute value

This index type uses only Mathlib's absolute values and algebra map.  Its
elements are precisely the absolute values on `L` extending `v` on `K`.
-/

namespace ClassFieldTheory

universe u v

/-- An absolute value on `L` whose restriction along `K → L` is `v`. -/
abbrev ExtendingAbsoluteValue
    {K : Type u} [Field K] (v : AbsoluteValue K ℝ)
    (L : Type v) [Field L] [Algebra K L] :=
  { w : AbsoluteValue L ℝ // ∀ a : K, w (algebraMap K L a) = v a }

end ClassFieldTheory
