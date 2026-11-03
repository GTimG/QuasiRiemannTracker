/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Adele/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.Coordinates
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteRestrictedProductBaseChange
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.InfinitePlaceTensorBlock
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralLocalFactor
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.LocalComponents
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedProduct

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/











set_option autoImplicit false

/-! # Adelic coordinates and restricted products -/
