/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/LocalClassFieldTheory/Finite/CyclotomicNorm/All.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.CyclotomicNorm.PrincipalUnits
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.CyclotomicNorm.StandardSubgroup
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.LocalClassFieldTheory.Finite.CyclotomicNorm.Unramified

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Norm groups of p-adic cyclotomic extensions

The prime-power and prime-to-`p` norm-subgroup computations used by local
Kronecker--Weber, exposed as reusable finite local class field theory.
-/
