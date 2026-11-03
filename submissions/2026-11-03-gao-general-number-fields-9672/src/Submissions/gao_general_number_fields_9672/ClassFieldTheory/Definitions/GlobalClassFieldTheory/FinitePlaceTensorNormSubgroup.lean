/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/GlobalClassFieldTheory/FinitePlaceTensorNormSubgroup.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
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
# Finite-place tensor-norm subgroup

The local algebra of `L / K` at a finite place `v` is
`K_v ⊗[K] L`.  Its determinant norm on units defines a subgroup of
`K_vˣ`.  This definition retains the whole tensor algebra, including all
factors above `v`; it does not choose a single completion of `L`.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The image of the determinant norm from the unit group of the finite-place
tensor algebra `K_v ⊗[K] L` into `K_vˣ`. -/
def finitePlaceTensorNormSubgroup
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  (Units.map (Algebra.norm (v.adicCompletion K) :
    (v.adicCompletion K ⊗[K] L) →* v.adicCompletion K)).range

end ClassFieldTheory

end
