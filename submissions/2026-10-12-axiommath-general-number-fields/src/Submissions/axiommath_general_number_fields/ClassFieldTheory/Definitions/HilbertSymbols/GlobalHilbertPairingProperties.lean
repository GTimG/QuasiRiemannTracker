/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/GlobalHilbertPairingProperties.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFiniteFactor
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Locality and support conditions for global Hilbert pairing families
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory.GlobalHilbertPairingFamily

universe u

/-- Every finite-place member of the family is a local Hilbert pairing. -/
def IsLocallyHilbert
    (F : Type u) [Field F] [NumberField F]
    {n : ℕ+} (B : GlobalHilbertPairingFamily F n) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F),
    HilbertPairing.IsLocalHilbertPairing (B v)

/-- For each pair of nonzero elements of the number field, only finitely many
finite-place factors are nontrivial. -/
def HasFiniteSupport
    (F : Type u) [Field F] [NumberField F]
    {n : ℕ+} (B : GlobalHilbertPairingFamily F n)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) : Prop :=
  ∀ a b : Fˣ,
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) ↦
      finiteFactor F B hmu v a b)

end ClassFieldTheory.GlobalHilbertPairingFamily
