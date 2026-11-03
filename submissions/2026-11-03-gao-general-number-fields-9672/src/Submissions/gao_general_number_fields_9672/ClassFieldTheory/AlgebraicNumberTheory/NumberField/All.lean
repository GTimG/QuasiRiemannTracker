/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/NumberField/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.CompletelySplitPrimes
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.CompletelySplitPrimesModFour
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.DegreeOnePrimes
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.IntegralPrimitiveElement
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.PlaceEquiv
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SchurPrimeDivisors
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedEtaleBridge
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.MathlibUnramifiedInterface
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.CompletelySplitFinset
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.GaloisDifferentBound
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.RootDiscriminantBound
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SupportedDiscriminantBound
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.NumberField.TameDifferentTrace

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


















set_option autoImplicit false

/-! # Finite and everywhere-unramified towers of number fields -/
