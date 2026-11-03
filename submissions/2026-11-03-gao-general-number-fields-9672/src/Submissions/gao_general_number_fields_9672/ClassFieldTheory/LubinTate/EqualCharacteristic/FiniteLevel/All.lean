/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/EqualCharacteristic/FiniteLevel/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/















set_option autoImplicit false

/-!
# Finite Lubin--Tate levels in equal characteristic

Public aggregate for division torsion, finite level fields, and their Galois
and norm structure.
-/
