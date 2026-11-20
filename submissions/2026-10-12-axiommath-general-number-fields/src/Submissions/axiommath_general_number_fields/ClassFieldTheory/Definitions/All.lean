/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.GlobalClassFieldTheory.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HasseArf.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HilbertSymbols.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.LocalClassFieldTheory.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.NormTheorems.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Class field theory definitions

Reader-facing vocabulary used by the headline theorem modules.  Primitive
leaves import Mathlib only; derived leaves import only the prerequisite
definition leaves.  Topic-level `All` modules and this root module are
aggregation-only, and no public definition imports an implementation module.
-/
