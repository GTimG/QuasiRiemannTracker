/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ComplexificationArtin/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceCompatibility
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceOverfield
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.NumberFieldComplexification
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.OverextensionArtin
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RamifiedOverextension
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RationalComplexification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Artin reciprocity for the cyclotomic complexification

This compatibility module reexports the semantic layers constructing the
rational fourth-root complexification, its compositum with a number field,
the complex-conjugation overextension at a ramified real place, and the
resulting infinite-place local-global Artin comparison.
-/
