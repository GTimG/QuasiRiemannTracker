/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/CharacterBounds/PrimitiveSmoothIdealSums.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LargeSieve.CharacterBounds.PrimitiveThetaSquareRootBound

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem initial_primitive_smooth_sum
    (F : Type) [Field F] [NumberField F]
    (hTC : NumberField.IsTotallyComplex F)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ f : Ideal (𝓞 F), f ≠ ⊥ →
      ∀ η : DedekindZetaZeroFree.RayClassCharacter F f,
        η.IsPrimitive → ¬η.IsPrincipal →
        ∀ X : ℝ, 0 < X →
          ‖initialTheta F η X‖ ≤ A * (Ideal.absNorm f : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
  obtain ⟨A, hA, hb⟩ := initial_primitive_sqrt_bound F hTC
  refine ⟨A, hA, fun f hf η hprim hnp X hX => ?_⟩
  have h := hb f hf η hprim hnp X hX
  have hN : (1 : ℝ) ≤ (Ideal.absNorm f : ℝ) := by
    have h0 : Ideal.absNorm f ≠ 0 := fun hz => hf (Ideal.absNorm_eq_zero_iff.mp hz)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  calc ‖initialTheta F η X‖
      ≤ A * Real.sqrt (Ideal.absNorm f : ℝ) := h
    _ ≤ A * (Ideal.absNorm f : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end DedekindZetaZeroFree.LargeSieve.Sieve
