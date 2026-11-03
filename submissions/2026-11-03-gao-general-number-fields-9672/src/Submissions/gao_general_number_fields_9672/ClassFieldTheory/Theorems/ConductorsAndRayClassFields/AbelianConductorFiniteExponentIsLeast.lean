/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/AbelianConductorFiniteExponentIsLeast.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.AbelianConductorFiniteNormCriterion
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
# The finite conductor exponent is a genuine local minimum

The local norm condition is satisfied at the conductor exponent and at
every larger exponent, and at no smaller exponent.  The norm is taken from
the whole completion tensor algebra, with no arbitrary place above `v`.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- The conductor exponent is the least index whose higher-unit group lies
in the finite-place tensor norm image. In particular this set is nonempty. -/
theorem IsAbelianConductor.finiteExponent_isLeast_tensorNorm
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {c : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (v : HeightOneSpectrum (𝓞 K)) :
    IsLeast (α := ℕ) (fun n =>
      rayLocalHigherUnitGroup v n ≤
        (Units.map (Algebra.norm (v.adicCompletion K)) :
          (v.adicCompletion K ⊗[K] L)ˣ →*
            (v.adicCompletion K)ˣ).range) (c.finitePart v) := by
  constructor
  · exact (hc.finiteExponent_le_iff_higherUnit_le_tensorNorm v
      (c.finitePart v)).mp le_rfl
  · intro n hn
    exact (hc.finiteExponent_le_iff_higherUnit_le_tensorNorm v n).mpr hn

end ClassFieldTheory

end
