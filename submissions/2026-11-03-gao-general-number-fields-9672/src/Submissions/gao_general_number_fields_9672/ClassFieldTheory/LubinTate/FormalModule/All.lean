/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/FormalModule/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.Intertwiner
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.LinearTerm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.Reduction
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.Series
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LubinTate.FormalModule.StandardSeries

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
