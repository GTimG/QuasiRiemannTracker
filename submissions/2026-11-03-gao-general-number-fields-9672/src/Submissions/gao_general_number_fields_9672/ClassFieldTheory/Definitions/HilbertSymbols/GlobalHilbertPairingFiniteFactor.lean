/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Definitions/HilbertSymbols/GlobalHilbertPairingFiniteFactor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFamily
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Finite-place factors of a global Hilbert pairing family
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalHilbertPairingFamily

universe u

/-- Evaluate a local pairing on two nonzero elements of the number field and
transport the resulting root of unity back to the number field. -/
def finiteFactor
    (F : Type u) [Field F] [NumberField F]
    {n : ℕ+} (B : GlobalHilbertPairingFamily F n)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    rootsOfUnity (n : ℕ) F := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
    rootsOfUnityEquivOfPrimitiveRoots
      (algebraMap F (v.adicCompletion F)).injective hmu
  exact e.symm
    (B v
      (powerClass (v.adicCompletion F) n
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a))
      (powerClass (v.adicCompletion F) n
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b)))

end ClassFieldTheory.GlobalHilbertPairingFamily

end
