/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HilbertSymbols/LocalHilbertPairingInverse.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import Mathlib.Algebra.Group.Hom.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Inverting the values of a local Hilbert pairing

The algebraic laws and norm-vanishing criterion are invariant under inversion
of every value. Thus these conditions alone do not distinguish the value
convention used by a normalized local Artin map. This theorem does not assert
that a pairing and its inverse are distinct.
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- Inverting every value preserves the local Hilbert-pairing axioms. -/
theorem IsLocalHilbertPairing.inv
    {K : Type u} [Field K] {n : ℕ+}
    {B : HilbertPairing K n}
    (hB : B.IsLocalHilbertPairing) :
    (B⁻¹).IsLocalHilbertPairing := by
  rcases hB with ⟨hsteinberg, hskew, hnondegenerate, hnorm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    simpa only [symbol, MonoidHom.inv_apply, inv_eq_one] using hsteinberg a ha
  · intro a b
    simpa only [MonoidHom.inv_apply] using
      congrArg (fun z : rootsOfUnity (n : ℕ) K => z⁻¹) (hskew a b)
  · constructor
    · intro a ha
      apply hnondegenerate.1 a
      intro b
      simpa only [MonoidHom.inv_apply, inv_eq_one] using ha b
    · intro b hb
      apply hnondegenerate.2 b
      intro a
      simpa only [MonoidHom.inv_apply, inv_eq_one] using hb a
  · intro a b
    simpa only [symbol, MonoidHom.inv_apply, inv_eq_one] using hnorm a b

end ClassFieldTheory.HilbertPairing
