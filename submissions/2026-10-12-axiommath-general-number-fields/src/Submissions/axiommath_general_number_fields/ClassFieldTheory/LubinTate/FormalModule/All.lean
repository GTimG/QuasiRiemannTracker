/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/FormalModule/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.Intertwiner
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.LinearTerm
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.Reduction
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.Series
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.FormalModule.StandardSeries

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/













set_option autoImplicit false

/-!
# Lubin--Tate formal modules

Public aggregate for the formal-series constructions used by Lubin--Tate
theory: composition, linear terms, intertwiners, coefficient equations,
reduction, the standard Lubin--Tate series, and the coefficientwise recursive
existence-and-uniqueness construction, including the resulting standard
commutative formal group and its coefficient-ring endomorphisms.
-/
