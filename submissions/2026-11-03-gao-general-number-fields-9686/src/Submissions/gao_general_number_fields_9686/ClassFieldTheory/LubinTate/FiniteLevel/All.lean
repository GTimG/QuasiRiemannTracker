/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/FiniteLevel/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.NormUniformizer
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/































set_option autoImplicit false

/-!
# General finite-level Lubin--Tate theory

Public aggregate for the characteristic-independent standard division
polynomials, primitive torsion fields, analytic formal-module action, explicit
finite Galois parameterization, integral-closure valuation, ramification
filtrations and their Herbrand formula, level-field tower, and the norm of a
primitive uniformizer.  It also exports stability of a standard level under
a principal-unit change of its defining uniformizer.
-/
