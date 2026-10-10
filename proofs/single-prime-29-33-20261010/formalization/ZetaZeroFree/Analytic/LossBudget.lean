import ZetaZeroFree.Exponent

/-!
Uniform finite loss budgets for §5. The scale/row exponent is defined in the
Exponent module; these lemmas retain the extra row range `d ≤ h + ζ` and make
the subsequent choice of the height exponent explicit. Analytic bounds must
still be supplied before these arithmetic budgets can be applied to the probe.
-/

namespace ZetaZeroFree.Analytic
noncomputable section
open Exponent

theorem R0_upper {δ : ℝ} (hδ : 0 ≤ δ) (hδu : δ ≤ 5 / 6) : R0 δ ≤ 1 := by
  have hd := denominator_positive hδu
  have hh : 0 ≤ 10 * δ / (3 * (5 - 2 * δ)) := by positivity
  unfold R0
  linarith

theorem slope_upper {δ : ℝ} (hδ : 0 ≤ δ) (hδu : δ ≤ 5 / 6) :
    slope δ ≤ 323 / 300 := by
  have hh := R0_upper hδ hδu
  unfold slope z0
  linarith

/-- The enlarged row cutoff has a uniform, explicitly bounded cost. -/
theorem E_le_with_buffer {δ β d ζ : ℝ}
    (hδ : 0 ≤ δ) (hδu : δ ≤ 5 / 6) (hζ : 0 ≤ ζ) (hd : d ≤ h + ζ) :
    E δ β d ≤ b - β + (323 / 300) * ζ := by
  have hs := (slope_positive hδ hδu).le
  have hu := slope_upper hδ hδu
  have hf := F0_le_boundary hδu
  have he := E_at_h δ β
  have hdiff := E_difference δ β d
  have hp := mul_nonneg (by linarith : 0 ≤ h + ζ - d) hs
  have hc := mul_nonneg hζ (sub_nonneg.mpr hu)
  nlinarith

/-- Choose all real and dyadic losses from the common gap, before the target. -/
theorem exists_common_row_budget {β A : ℝ} (hβ : b < β) (hA : 0 ≤ A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ δ d : ℝ, 0 ≤ δ → δ ≤ 5 / 6 → d ≤ h + η →
        E δ β d + A * η ≤ -(3 / 4) * (β - b) := by
  let C : ℝ := 323 / 300
  let η := (β - b) / (4 * (C + A + 1))
  have hC : 0 < C := by norm_num [C]
  have hden : 0 < 4 * (C + A + 1) := by positivity
  have hη : 0 < η := div_pos (sub_pos.mpr hβ) hden
  have heq : (4 * (C + A + 1)) * η = β - b := by
    dsimp [η]
    field_simp
  refine ⟨η, hη, ?_⟩
  intro δ d hδ hδu hd
  have he := E_le_with_buffer (β := β) hδ hδu hη.le hd
  change E δ β d ≤ b - β + C * η at he
  nlinarith

/-- Fixed polynomial height orders can be absorbed by choosing height last. -/
theorem exists_height_budget {μ N : ℝ} (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ τ : ℝ, 0 < τ ∧ N * τ ≤ μ / 8 := by
  let τ := μ / (8 * (N + 1))
  have hden : 0 < 8 * (N + 1) := by positivity
  have hτ : 0 < τ := div_pos hμ hden
  have heq : (8 * (N + 1)) * τ = μ := by
    dsimp [τ]
    field_simp
  exact ⟨τ, hτ, by nlinarith⟩

/-- Common real losses precede target-dependent polynomial height orders. -/
theorem exists_common_row_then_height_budget {β A : ℝ}
    (hβ : b < β) (hA : 0 ≤ A) :
    ∃ η : ℝ, 0 < η ∧ ∀ N : ℝ, 0 ≤ N →
      ∃ τ : ℝ, 0 < τ ∧
        ∀ δ d : ℝ, 0 ≤ δ → δ ≤ 5 / 6 → d ≤ h + η →
          E δ β d + A * η + N * τ ≤ -(5 / 8) * (β - b) := by
  obtain ⟨η, hη, he⟩ := exists_common_row_budget hβ hA
  refine ⟨η, hη, ?_⟩
  intro N hN
  obtain ⟨τ, hτ, ht⟩ := exists_height_budget (sub_pos.mpr hβ) hN
  refine ⟨τ, hτ, ?_⟩
  intro δ d hδ hδu hd
  linarith [he δ d hδ hδu hd]

end
end ZetaZeroFree.Analytic
