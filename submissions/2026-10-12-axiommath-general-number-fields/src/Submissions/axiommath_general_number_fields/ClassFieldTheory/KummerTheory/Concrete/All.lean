/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/KummerTheory/Concrete/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.KummerTheory.Concrete.CyclotomicPrimeBaseChange
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.KummerTheory.Concrete.FinitePlaceDecomposition
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.KummerTheory.Concrete.SUnitKummerUnramified
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.All
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.KummerTheory.Concrete.SimpleExtensionLocalBehavior

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Concrete Kummer theory

Root characters, radical quotients, finite and infinite generation, the local
unramified unit criterion, and the perfect Kummer pairing for actual field
extensions.
-/
