/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/NormTheorems/GlobalNormIsEverywhereLocalNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.NormTheorems.IsEverywhereLocalNorm
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.NormTheorems.TensorNormBaseChange

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Global norms are local norms everywhere

This module states the elementary local consequence of being a global field
norm.  The assumptions give a finite extension `L / K` of number fields and
a unit `x` of `K`.  The conclusion says that if `x` lies in the
global norm subgroup, then after scalar extension it is a determinant norm
at every finite and every infinite completion of `K`.
-/

open scoped NumberField

namespace ClassFieldTheory

universe u v

/-- Every global field norm is a norm over every completion. -/
theorem globalNorm_isEverywhereLocalNorm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (x : Kˣ) :
    IsFieldNorm K L x → IsEverywhereLocalNorm K L x := by
  rintro ⟨y, rfl⟩
  constructor
  · intro w
    refine ⟨Units.map
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.adicCompletion K) (B := L)).toRingHom y, ?_⟩
    change Algebra.norm (w.adicCompletion K)
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.adicCompletion K) (B := L) (y : L)) =
        algebraMap K (w.adicCompletion K) (Algebra.norm K (y : L))
    exact tensorNorm_includeRight K L (w.adicCompletion K) y
  · intro w
    refine ⟨Units.map
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.Completion) (B := L)).toRingHom y, ?_⟩
    change Algebra.norm w.Completion
      (Algebra.TensorProduct.includeRight
        (R := K) (A := w.Completion) (B := L) (y : L)) =
        algebraMap K w.Completion (Algebra.norm K (y : L))
    exact tensorNorm_includeRight K L w.Completion y

end ClassFieldTheory
