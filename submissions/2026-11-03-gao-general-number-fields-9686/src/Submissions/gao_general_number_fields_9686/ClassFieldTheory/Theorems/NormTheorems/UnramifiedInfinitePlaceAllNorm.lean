/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/NormTheorems/UnramifiedInfinitePlaceAllNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Norms at an unramified infinite place

For a finite abelian extension, the determinant norm from the whole
archimedean tensor algebra is surjective when the base place is
unramified in the extension.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every nonzero base-field element is an archimedean tensor norm at an
unramified infinite place of a finite abelian extension. -/
theorem isNormAtInfinitePlace_of_unramified
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : InfinitePlace K) (hv : v.IsUnramifiedIn L) (x : Kˣ) :
    IsNormAtInfinitePlace K L v x := by
  have htop : infiniteTensorNormSubgroup (K := K) (L := L) v = ⊤ :=
    (GlobalClassFieldTheory.GlobalClassFields.infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
      (K := K) (L := L) v).2 hv
  let xv : v.Completionˣ := Units.map (algebraMap K v.Completion) x
  have hnorm : xv ∈ infiniteTensorNormSubgroup (K := K) (L := L) v := by
    rw [htop]
    trivial
  obtain ⟨y, hy⟩ := hnorm
  exact ⟨y, congrArg Units.val hy⟩

end ClassFieldTheory

end
