/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/NormTheorems/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.CyclicHasseNormTheorem
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.CompletionTensorNormDecomposition
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.CompletionTensorNormDecompositionCanonical
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.GlobalNormIsEverywhereLocalNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.ComplexInfinitePlaceAllNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.InfiniteNormIffPositive
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.NegativeOneNotInfiniteNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.UnramifiedInfinitePlaceAllNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.TensorNormBaseChange

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/











set_option autoImplicit false

/-!
# Local-to-global norm theorems

This module gathers the public local-global principles for field norms.
-/
