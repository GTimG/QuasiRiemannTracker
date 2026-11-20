/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.All

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Global class field theory

This aggregate imports the implementation modules for global Artin reciprocity,
the class-field correspondence, Hilbert and power-residue reciprocity, ideal
Artin maps, decomposition, and principalization.  Reader-facing statements are
collected in `ClassFieldTheory.Theorems.GlobalClassFieldTheory.All`.
-/
