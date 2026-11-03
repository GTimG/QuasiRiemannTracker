/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/NormTheorems/ComplexInfinitePlaceAllNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Norms at a complex infinite place

The positivity condition is vacuous at a complex place. Consequently every
nonzero base-field element is a determinant norm from the whole archimedean
tensor algebra.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The determinant norm from `K_v ⊗_K L` is surjective on the image of
`Kˣ` when `v` is complex. -/
theorem isNormAtInfinitePlace_of_complex
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (v : InfinitePlace K) (hv : v.IsComplex) (x : Kˣ) :
    IsNormAtInfinitePlace K L v x := by
  let xv : v.Completionˣ := Units.map (algebraMap K v.Completion) x
  have hpos : xv ∈ RayClass.infinitePositiveSubgroup v := by
    intro hr
    exact ((InfinitePlace.not_isReal_iff_isComplex).2 hv hr).elim
  have hnorm : xv ∈ infiniteTensorNormSubgroup (K := K) (L := L) v :=
    infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
      (K := K) (L := L) v hpos
  obtain ⟨y, hy⟩ := hnorm
  exact ⟨y, congrArg Units.val hy⟩

end ClassFieldTheory

end
