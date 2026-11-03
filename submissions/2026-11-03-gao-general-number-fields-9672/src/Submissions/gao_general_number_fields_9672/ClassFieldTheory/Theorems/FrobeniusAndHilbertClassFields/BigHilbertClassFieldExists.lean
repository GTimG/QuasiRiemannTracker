/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/BigHilbertClassFieldExists.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
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
# Existence of the big Hilbert class field

The big Hilbert class field is characterized intrinsically as a finite
abelian extension unramified at every finite prime and containing every
other finite abelian extension with that property.  No particular field
chosen by the implementation appears in the statement.
-/

open scoped NumberField

namespace ClassFieldTheory

/-- A maximal finite-prime-unramified finite abelian extension exists. -/
theorem exists_bigHilbertClassField
    (K : Type) [Field K] [NumberField K] :
    ∃ E : FiniteAbelianExtension K, IsBigHilbertClassField E :=
  GlobalClassFieldComparison.exists_bigHilbertClassField K

end ClassFieldTheory
