/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: vendor/class-field-theory/Lean4/ClassFieldTheory/Theorems/HilbertSymbols/KummerAlgebraOneNormSurjective.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebraNormSubgroup
public import Submissions.gao_general_number_fields_9686.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The reducible Kummer algebra at one

Even when its rank is `n`, the algebra `K[X]/(Xⁿ-1)` has surjective norm
under the local Kummer hypotheses. This is the simplest instance showing
that norm index and algebra rank are different invariants.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- The Kummer algebra defined by `Xⁿ-1` has full unit norm image. -/
theorem kummerAlgebraNormSubgroup_one_eq_top
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    kummerAlgebraNormSubgroup K n 1 = ⊤ := by
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
  have hmuS : (primitiveRoots (n : ℕ) S).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    refine ⟨e.symm ζ, ?_⟩
    exact (mem_primitiveRoots n.pos).2
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective e.symm.injective)
  let B₀ : HilbertPairing S n := localHilbertPairing S n hnS hmuS
  let B : HilbertPairing K n := hilbertPairingOfRingEquiv e n hmuS B₀
  have hB : HilbertPairing.IsLocalHilbertPairing B :=
    hilbertPairingOfRingEquiv_isLocalHilbertPairing e n hmuS B₀
      (localHilbertPairing_isLocalHilbertPairing S n hnS hmuS)
  apply top_unique
  intro b _
  have hbNorm : IsKummerNorm K n 1 b :=
    (hB.2.2.2 1 b).1 (by simp [HilbertPairing.symbol])
  obtain ⟨y, hy⟩ := hbNorm
  refine ⟨y, ?_⟩
  apply Units.ext
  exact hy

end ClassFieldTheory

end
