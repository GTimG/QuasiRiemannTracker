/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/NormTheorems/IsNormAtFinitePlace.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Norms at finite places
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- A unit of `K` is a norm at a finite place `w` if its image in `K_w` is a
determinant norm from `K_w ⊗_K L`. -/
def IsNormAtFinitePlace
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : Prop :=
  ∃ y : (w.adicCompletion K ⊗[K] L)ˣ,
    Algebra.norm (w.adicCompletion K)
        (y : w.adicCompletion K ⊗[K] L) =
      algebraMap K (w.adicCompletion K) (x : K)

end ClassFieldTheory
