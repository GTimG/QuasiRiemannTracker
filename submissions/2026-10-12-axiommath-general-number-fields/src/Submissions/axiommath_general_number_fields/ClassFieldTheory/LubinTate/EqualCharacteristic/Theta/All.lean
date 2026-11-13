/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LubinTate/EqualCharacteristic/Theta/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# The theta construction in equal-characteristic Lubin--Tate theory

Public aggregate for theta coefficients, the theta series, evaluation, and
the first theta identity.
-/
