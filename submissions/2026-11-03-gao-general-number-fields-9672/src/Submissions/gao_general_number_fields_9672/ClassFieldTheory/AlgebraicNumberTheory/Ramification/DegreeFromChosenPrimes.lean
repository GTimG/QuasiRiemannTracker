/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Ramification/DegreeFromChosenPrimes.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.AlgebraicNumberTheory.Ramification.DegreeProduct
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.RamificationTheory.HilbertRamification.Dedekind.ChosenInertiaCoverage
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.RamificationTheory.HilbertRamification.Dedekind.InertiaGeneration

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Global degree bound from chosen finite-prime inertia groups

This combines three generic steps in the global degree estimate: coverage by one
prime over each member of `S`, generation of the full Galois group by all
finite-prime inertia, and the finite abelian product bound.
-/

noncomputable section

namespace AlgebraicNumberTheory.Ramification

open NumberField
open HilbertRamification.Dedekind
open scoped NumberField IsMulCommutative

/-- The generic global degree estimate used by the concrete inertia-field
compositum. -/
theorem finrank_le_totient_prod_primePowers_of_chosen_primes
    (M : Type) [Field M] [NumberField M] [IsAbelianGalois ℚ M]
    (S : Finset Nat.Primes) (e : Nat.Primes → ℕ)
    (chosen : ∀ p : Nat.Primes,
      Ideal.primesOver (rationalPrimeIdeal p) (𝓞 M))
    (hunramifiedOutside :
      ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.IsMaximal],
        (¬ ∃ p ∈ S, rationalPrimeIdeal p = Q.under ℤ) →
          Algebra.IsUnramifiedAt ℤ Q)
    (hcard : ∀ p ∈ S,
      Nat.card
          (inertiaGroup (chosen p).1 (M ≃ₐ[ℚ] M)) ≤
        Nat.totient (p.1 ^ e p)) :
    Module.finrank ℚ M ≤
      Nat.totient (∏ p ∈ S, p.1 ^ e p) := by
  let I : Nat.Primes → Subgroup (M ≃ₐ[ℚ] M) :=
    fun p ↦ inertiaGroup (chosen p).1 (M ≃ₐ[ℚ] M)
  have hcoverage :
      ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.IsMaximal],
        inertiaGroup Q (M ≃ₐ[ℚ] M) ≤ S.sup I :=
    inertiaGroup_le_finsetSup_chosen_of_unramified_outside
      S chosen hunramifiedOutside
  have hgenerate : S.sup I = ⊤ :=
    subgroup_eq_top_of_forall_inertiaGroup_le (S.sup I) hcoverage
  exact finrank_le_totient_prod_primePowers_of_inertia_bounds
    M S e I hgenerate hcard

end AlgebraicNumberTheory.Ramification

end
