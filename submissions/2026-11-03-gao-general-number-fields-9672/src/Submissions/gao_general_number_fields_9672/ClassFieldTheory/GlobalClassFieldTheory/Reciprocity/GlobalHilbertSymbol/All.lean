/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.Core
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceCharacterComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceFiniteSupport
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceLocalGlobal
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlace
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceCharacter
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceNegative
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceNegativeRoot
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceNegativeUnit
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlacePositive
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceRamification
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceRealComparison
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlaceRealSquare

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
















set_option autoImplicit false

/-!
# Global-place Hilbert symbols

Public aggregate for the finite-place Kummer character comparison, finite
support of the Hilbert factors, and the infinite-place comparison.
-/
