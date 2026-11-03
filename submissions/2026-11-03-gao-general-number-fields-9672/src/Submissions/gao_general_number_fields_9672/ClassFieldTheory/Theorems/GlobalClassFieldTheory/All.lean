/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/GlobalClassFieldTheory/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocity
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocityQuotient
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquivMk
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceLocalGlobalNormKernel
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinNormKernel
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinDecomposition
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceCompletionLocalArtin
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinLocalValue
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.TopologicalGlobalReciprocity
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.GlobalClassFieldTheory.MaximalAbelianGlobalArtin

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/












set_option autoImplicit false

/-!
# Global class field theory

This module collects finite ideal-theoretic reciprocity and the topological
maximal-abelian statements. The latter are proved via topological comparison
with the existing restricted-product implementation.
-/
