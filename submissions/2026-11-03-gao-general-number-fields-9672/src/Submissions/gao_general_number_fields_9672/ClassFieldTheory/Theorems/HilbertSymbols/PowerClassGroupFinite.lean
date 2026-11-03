/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HilbertSymbols/PowerClassGroupFinite.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
public import Submissions.gao_general_number_fields_9672.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
public import Submissions.gao_general_number_fields_9672.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Finiteness of local power classes

The nonzero residue of the exponent in a nonarchimedean local field makes its
multiplicative `n`-th-power quotient finite. This is the finiteness input for
turning a nondegenerate Hilbert pairing into a perfect pairing.
-/

namespace ClassFieldTheory

universe u

/-- The power-class group of a nonarchimedean local field is finite when
the exponent is nonzero in the field. -/
theorem powerClassGroup_finite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) :
    Finite (PowerClassGroup K n) := by
  let : Small.{0} K := LocalFieldTheory.nonarchimedeanLocalField_small K
  let S := Shrink.{0} K
  let : ValuativeRel S := LocalFieldTheory.shrinkLocalFieldValuativeRel K
  let : IsNonarchimedeanLocalField S :=
    LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField K
  let e : S ≃+* K := Shrink.ringEquiv K
  have hnS : ((n : ℕ) : S) ≠ 0 := by
    intro hz
    apply hnK
    have hzK := congrArg e hz
    simpa [e] using hzK
  let : Finite (PowerClassGroup S n) := by
    change Finite (Sˣ ⧸ (powMonoidHom (n : ℕ) : Sˣ →* Sˣ).range)
    exact LocalFieldTheory.finite_nthPowerQuotient_of_natCast_ne_zero
      S (n : ℕ) hnS
  exact Finite.of_equiv (PowerClassGroup S n)
    (powerClassGroupEquivOfRingEquiv e n).toEquiv

end ClassFieldTheory
