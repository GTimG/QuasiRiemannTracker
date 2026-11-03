/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/FrobeniusAndHilbertClassFields/BigHilbertClassFieldPrimeSplittingPositivePrincipal.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldPrimeSplitting

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Totally positive principal primes and splitting

A finite prime splits completely in the big Hilbert class field exactly
when its fractional ideal has a totally positive generator.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- Equivalently, a prime splits completely in the big Hilbert class field
exactly when it has a totally positive generator. -/
theorem finitePrime_splitsCompletelyInBigHilbertClassField_iff_positivePrincipal
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePrimeSplitsCompletely K E v ↔
      ∃ x : Kˣ,
        (∀ w : RayClassRealPlace K,
          0 < w.1.embedding_of_isReal w.2 (x : K)) ∧
        toPrincipalIdeal (𝓞 K) K x = finitePrimeFractionalIdeal v := by
  rw [finitePrime_splitsCompletelyInBigHilbertClassField_iff K E hE v]
  change ((⟨finitePrimeFractionalIdeal v, _⟩ :
    rayClassPrimeToIdeals (narrowRayClassModulus K)) :
      RayClassGroup (narrowRayClassModulus K)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change finitePrimeFractionalIdeal v ∈
    rayPrincipalIdealSubgroup (narrowRayClassModulus K) ↔ _
  rw [mem_rayPrincipalIdealSubgroup_iff]
  simp [IsRayCongruent, narrowRayClassModulus]

end ClassFieldTheory

end
