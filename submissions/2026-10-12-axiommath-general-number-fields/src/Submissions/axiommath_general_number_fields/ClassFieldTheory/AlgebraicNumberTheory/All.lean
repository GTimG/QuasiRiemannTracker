/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Adele.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Completion.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.CompositumEmbedding
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Galois.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Idele.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.NumberField.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.Ramification.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.RayClass.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.SUnit.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.AlgebraicNumberTheory.TensorProduct

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




















set_option autoImplicit false

/-!
# Algebraic number theory

Public root for the reusable global algebraic-number-theory layer used by
class field theory. It exports finite abelian composita, idèles and idèle
classes in extensions, normal-closure and splitting results, ray class groups,
S-units, and the ramification and degree results needed by global applications.
-/
