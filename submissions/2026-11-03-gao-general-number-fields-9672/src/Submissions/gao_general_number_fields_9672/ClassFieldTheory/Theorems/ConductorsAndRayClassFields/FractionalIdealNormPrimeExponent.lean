/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/FractionalIdealNormPrimeExponent.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Prime exponents of a fractional-ideal norm

At a finite prime of the base, the exponent of the norm is the sum of the
upstairs exponents, each weighted by its inertia degree.  This is the
calculation needed when passing from ideals to norm-defined ray subgroups.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The exponent at `v` of an ideal norm is the inertia-degree-weighted sum
of the exponents at the primes lying above `v`. -/
theorem fractionalIdealNorm_primeExponent
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (I : NumberFieldFractionalIdealGroup L)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        ((fractionalIdealNorm K L I : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (NumberFieldFractionalIdealGroup.countVector I).sum fun W n =>
        if fractionalIdealNormPrimeBelow K L W = v then
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n
        else 0 := by
  exact fractionalIdealNorm_count K L I v

end ClassFieldTheory

end
