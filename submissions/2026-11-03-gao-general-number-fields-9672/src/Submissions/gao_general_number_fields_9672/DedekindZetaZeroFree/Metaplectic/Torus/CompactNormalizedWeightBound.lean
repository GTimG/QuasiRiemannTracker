/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Torus/CompactNormalizedWeightBound.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Torus.NormTwistedPeriodizationAndAveraging

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.RepresentationTheory.torus_weighted_chart_quantitative_prove
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem delta_real_continuous : Continuous (fun t : E F ζ hζ =>
    (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ))) := by
  have hc := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))
  have he : (fun t : E F ζ hζ => (((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ))) =
      (fun t : E F ζ hζ => (((KPGlobalCenterRationalCharacter.nu F ζ hζ t : ℝ≥0) : ℝ)) ^ (6 : ℕ)) := by
    funext t
    rw [KPGlobalCenterRationalCharacter.nu_formula, ← Real.rpow_natCast, ← Real.rpow_mul]
    · norm_num [KPGlobalTorusFunctionData.delta]
    · exact NNReal.coe_nonneg _
  rw [he]
  exact hc.pow 6

theorem normalized_weight_continuous (C : ModelData F ζ hζ) (s : ℂ) :
    Continuous (fun b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C =>
      ‖(((((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) : ℂ) *
        (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val)⁻¹)‖) := by
  have hh : Continuous (fun b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C =>
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val) :=
    Complex.continuous_ofReal.comp
      ((delta_real_continuous F ζ hζ).sqrt.comp continuous_subtype_val)
  have hn : ∀ b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C,
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val ≠ 0 := by
    intro b
    unfold KPGlobalTorusFunctionData.deltaHalf
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2
      (NNReal.coe_pos.2 (pos_iff_ne_zero.2
        (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ b.val))))))
  exact ((Units.continuous_val.comp
    (Continuous.inv (twist F ζ hζ (productModel F ζ hζ C) s).character.continuous)).mul
      (hh.inv₀ hn)).norm

theorem compact_normalized_weight_bound (C : ModelData F ζ hζ) (s : ℂ)
    (L : Set (KPGlobalTorusPeriodizationInverse.B F ζ hζ C)) (hL : IsCompact L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ b ∈ L,
      ‖(((((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) : ℂ) *
        (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val)⁻¹)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hL.bddAbove_image
    (normalized_weight_continuous F ζ hζ C s).continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro b hb
  exact (hB (Set.mem_image_of_mem _ hb)).trans (le_max_right _ _)

end
end DedekindZetaZeroFree.RepresentationTheory.torus_weighted_chart_quantitative_prove
