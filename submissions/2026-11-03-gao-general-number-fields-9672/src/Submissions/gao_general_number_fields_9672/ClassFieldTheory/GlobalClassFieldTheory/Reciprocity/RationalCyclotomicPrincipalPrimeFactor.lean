/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalCyclotomicPrincipalPrimeFactor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalAwayProduct

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The ramified prime factor of a rational cyclotomic principal idele

The level-zero factor is trivial.  At every positive level, the finite-place
character specification reduces the claim to the ramified chosen-Artin formula
proved in `RationalCyclotomicFinitePlaceArtin`.
-/

open scoped Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The chosen finite-place factor at the ramified prime `p` is the direct
reduction of the rational `p`-adic unit. -/
theorem rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) := by
  cases k with
  | zero =>
      apply Units.ext
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
  | succ n =>
      exact
        rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime_succ_formula
          p n x

end Reciprocity
end GlobalClassFieldTheory

end
