/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/NumberFieldFractionalIdealGroup.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Fractional-ideal group of a number field
-/

open scoped NumberField
open NumberField

namespace ClassFieldTheory

universe u

/-- The group of nonzero fractional ideals of a number field. -/
abbrev NumberFieldFractionalIdealGroup
    (K : Type u) [Field K] [NumberField K] :=
  (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ

end ClassFieldTheory
