/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.MathlibNormInterface
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitSubgroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.KummerLocalNormContainment
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.All
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitLocalPowerMap
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SupportedIdelePowerLocalUnitQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/













set_option autoImplicit false

/-!
# The global class-field axiom and its arithmetic consequences

This aggregate exports the cyclic idele-class norm-index calculation, the
Hasse norm principle, and the rational idele-class formation.
-/
