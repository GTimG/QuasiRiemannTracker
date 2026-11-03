/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassOfFinitePrime.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Prime classes in ray class groups
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

 lemma finitePrimeFractionalIdeal_mem_primeTo
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    finitePrimeFractionalIdeal v ∈ rayClassPrimeToIdeals m := by
  intro w hw
  exact FractionalIdeal.count_maximal_coprime K w fun h => (h ▸ hv) hw

/-- The class in the ray class group represented by a finite prime away from
the modulus. -/
def rayClassOfFinitePrime
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) : RayClassGroup m :=
  QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
    ⟨finitePrimeFractionalIdeal v, finitePrimeFractionalIdeal_mem_primeTo m v hv⟩

/-- The ordinary ideal class represented by a finite prime. -/
def ordinaryRayClassOfFinitePrime
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClassGroup (ordinaryRayClassModulus K) :=
  rayClassOfFinitePrime (ordinaryRayClassModulus K) v (by
    simp [ordinaryRayClassModulus])

/-- The narrow ideal class represented by a finite prime. -/
def narrowRayClassOfFinitePrime
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClassGroup (narrowRayClassModulus K) :=
  rayClassOfFinitePrime (narrowRayClassModulus K) v (by
    simp [narrowRayClassModulus])

end ClassFieldTheory

end
