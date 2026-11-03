/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/SmallHilbertClassFieldExists.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Existence of the small Hilbert class field

The small Hilbert class field is characterized as an everywhere-unramified
finite abelian extension containing every other such extension.  In
particular, real places are required to remain unramified.
-/

open scoped NumberField

namespace ClassFieldTheory

/-- A maximal everywhere-unramified finite abelian extension exists. -/
theorem exists_smallHilbertClassField
    (K : Type) [Field K] [NumberField K] :
    ∃ E : FiniteAbelianExtension K, IsSmallHilbertClassField E :=
  GlobalClassFieldComparison.exists_smallHilbertClassField K

end ClassFieldTheory
