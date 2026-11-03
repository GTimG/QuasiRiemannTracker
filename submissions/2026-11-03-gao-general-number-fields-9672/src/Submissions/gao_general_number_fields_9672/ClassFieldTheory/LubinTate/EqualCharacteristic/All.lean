/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/EqualCharacteristic/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/











set_option autoImplicit false

/-!
# Equal-characteristic Lubin--Tate theory

Public aggregate for the equal-characteristic Lubin--Tate construction.  It
includes the Laurent-series model, finite and completed Lubin--Tate levels,
and the Frobenius and theta constructions.  The local-class-field-theory
norm-subgroup calculation and its transport live in
`LocalClassFieldTheory.LubinTateApplication`.

Each mathematical stage has a reader-facing aggregate below
`LubinTate.EqualCharacteristic`; declarations remain in the matching
namespace.
-/
