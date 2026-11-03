/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Compositum
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.EqualCharacteristic
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.EqualCharacteristicStandardCompositum
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.InertiaUnramifiedExtension
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.StandardCompositum
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Unramified

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/











set_option autoImplicit false

/-!
# Filtered finite local reciprocity

Public aggregate for the filtered Artin-map API and its unramified,
equal-characteristic, compositum, and finite-Abelian specializations.
-/
