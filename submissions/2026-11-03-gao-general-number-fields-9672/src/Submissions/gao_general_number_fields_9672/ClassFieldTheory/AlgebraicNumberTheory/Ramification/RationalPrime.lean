/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/AlgebraicNumberTheory/Ramification/RationalPrime.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Rational prime ideals

This file identifies the height-one ideal of `ℤ` attached to a positive
rational prime with its usual principal ideal.
-/

noncomputable section

namespace AlgebraicNumberTheory.Ramification

/-- The height-one ideal of `ℤ` corresponding to a positive rational prime. -/
abbrev rationalPrimeIdeal (p : Nat.Primes) : Ideal ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv.symm p).asIdeal

/-- The height-one ideal represented by a positive rational prime is its
usual principal ideal. -/
theorem rationalPrimeIdeal_eq_span (p : Nat.Primes) :
    rationalPrimeIdeal p = Ideal.span {(p.1 : ℤ)} := by
  let v : IsDedekindDomain.HeightOneSpectrum ℤ :=
    Rat.HeightOneSpectrum.primesEquiv.symm p
  have hgen : Rat.HeightOneSpectrum.natGenerator v = p.1 := by
    have h := congrArg Subtype.val
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply p)
    exact h
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext z
    simp
  change v.asIdeal = Ideal.span {(p.1 : ℤ)}
  symm
  calc
    Ideal.span {(p.1 : ℤ)} =
        Ideal.span
          {(Rat.HeightOneSpectrum.natGenerator v : ℤ)} := by rw [hgen]
    _ = v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) :=
      Rat.HeightOneSpectrum.span_natGenerator v
    _ = v.asIdeal := by
      rw [he]
      change v.asIdeal.map (RingHom.id ℤ) = v.asIdeal
      exact Ideal.map_id _

end AlgebraicNumberTheory.Ramification

end
