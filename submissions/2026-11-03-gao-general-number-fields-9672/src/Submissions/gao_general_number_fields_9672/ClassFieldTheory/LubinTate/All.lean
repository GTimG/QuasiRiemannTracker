/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.EqualCharacteristic.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FiniteLevel.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.All
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.Padic.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Lubin--Tate theory

This is the public aggregate for Lubin--Tate theory.  It exports the formal
module foundations, the characteristic-independent standard finite-level
division fields and their lower/upper ramification formulas, and the explicit
equal-characteristic construction.  The
norm-subgroup calculation and transport used by local class field theory are
exported from `LocalClassFieldTheory.LubinTateApplication`, and the
field-facing existence theorem from
`LocalClassFieldTheory.Finite.Existence.EqualCharacteristic`.
The equal-characteristic construction is organized by its mathematical stages
below `LubinTate.EqualCharacteristic`.
-/
