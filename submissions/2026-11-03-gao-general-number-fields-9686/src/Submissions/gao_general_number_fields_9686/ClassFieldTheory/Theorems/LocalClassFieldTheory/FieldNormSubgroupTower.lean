/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/FieldNormSubgroupTower.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Norm subgroups in a tower

The norm from a larger field factors through the norm from every intermediate
field. Thus enlarging a finite extension can only shrink its subgroup of
norms in the base field. No local-field or Galois assumption is needed.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w

/-- In a finite tower `K ⊆ M ⊆ L`, every norm from `L` to `K` is a norm
from `M` to `K`. -/
theorem fieldNormSubgroup_le_of_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L] :
    fieldNormSubgroup K L ≤ fieldNormSubgroup K M := by
  rintro x ⟨y, rfl⟩
  refine ⟨fieldNormHom M L y, ?_⟩
  apply Units.ext
  exact Algebra.norm_norm

end ClassFieldTheory

end
