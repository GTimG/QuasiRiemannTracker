/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/FieldNormSubgroupRingEquiv.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupRingEquiv
public import Mathlib.Algebra.Group.Subgroup.Map

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Norm membership under compatible field equivalences

Transporting both fields of a finite extension through compatible ring
equivalences preserves the actual field norms, not merely their index.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w x

/-- An element is a field norm exactly when its image under a compatible
base-field equivalence is a field norm in the transported extension. -/
theorem mem_fieldNormSubgroup_iff_ringEquiv
    {F : Type u} {M : Type v} {F' : Type w} {M' : Type x}
    [Field F] [Field M] [Field F'] [Field M']
    [Algebra F M] [Algebra F' M']
    [FiniteDimensional F M] [FiniteDimensional F' M']
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M))
    (a : Fˣ) :
    a ∈ fieldNormSubgroup F M ↔
      (Units.mapEquiv eF.toMulEquiv) a ∈ fieldNormSubgroup F' M' := by
  rw [← fieldNormSubgroup_map_ringEquiv eF eM he]
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end ClassFieldTheory

end
