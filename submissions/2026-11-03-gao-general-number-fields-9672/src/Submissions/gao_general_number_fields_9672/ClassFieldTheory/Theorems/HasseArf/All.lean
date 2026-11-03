/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HasseArf/All.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.HasseArf
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionAtLowerIndexStrictMono
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionAtLowerIndexDifference
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionAtLowerIndexNatOfJump
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionCanonical
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionInverseHerbrandFunction
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.HerbrandFunctionNat
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.InverseHerbrandFunctionHerbrandFunction
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.IsUpperRamificationJumpInt
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.LowerRamificationGroupAntitone
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.LowerRamificationGroupEventuallyBot
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.LowerRamificationGroupNormal
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.LowerRamificationGroupZeroEqInertia
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.RealLowerRamificationGroupCanonical
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.RealLowerRamificationGroupNat
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.RealLowerRamificationGroupNormal
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.RealAndUpperRamificationGroupNormal
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.UpperRamificationGroupAntitone
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.UpperRamificationGroupCanonical
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.UpperRamificationGroupAfter
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.HasseArf.UpperRamificationGroupEventuallyBot

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/























set_option autoImplicit false

/-! Public Hasse--Arf theorem and basic lower-filtration identities. -/
