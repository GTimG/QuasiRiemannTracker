/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/IsAbelianConductor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.EmbedsInRayClassField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Conductors of finite abelian extensions
-/

namespace ClassFieldTheory

universe u v

/-- A modulus is the conductor of a finite abelian extension when it is
exactly the least modulus whose ray class field contains the extension. -/
def IsAbelianConductor
    (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    (c : RayClassModulus K) : Prop :=
  ∀ m : RayClassModulus K,
    EmbedsInRayClassField K L m ↔ c ≤ m

end ClassFieldTheory
