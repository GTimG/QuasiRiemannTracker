/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal P.3 short reference geometry, independent of an analytic supplier. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open Filter

def shortWidth : ℝ := 23/200

theorem shortWidth_pos : 0 < shortWidth := by norm_num [shortWidth]

/-- Squaring the ordinary column and duplicating the ORIGINAL selected
slots gives total column exponent twice the unsquared width. The first
Poisson pair modulus is the square of that length. -/
theorem fourth_conductor_identity (b w : ℝ) : 2*(2*b+2*w) = 4*(b+w) := by ring

/-- The actual equal-product companion retains its original product. -/
theorem equal_product_reference {U X₁ X₂ : ℝ} (hU : 0 < U)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    0 < U^shortWidth ∧ 0 < X₁*X₂/U^shortWidth ∧
      U^shortWidth*(X₁*X₂/U^shortWidth) = X₁*X₂ := by
  have hp := Real.rpow_pos_of_pos hU shortWidth
  refine ⟨hp,div_pos (mul_pos hX₁ hX₂) hp,?_⟩
  field_simp

/-- Exhaustive P.3 dispatch on the original positive scales. -/
theorem reference_dispatch (U X₁ X₂ : ℝ) :
    X₁ ≤ U^shortWidth ∨ X₂ ≤ U^shortWidth ∨
      U^shortWidth < X₁ ∧ U^shortWidth < X₂ := by
  rcases le_or_gt X₁ (U^shortWidth) with h | h
  · exact Or.inl h
  · rcases le_or_gt X₂ (U^shortWidth) with h₂ | h₂
    · exact Or.inr (Or.inl h₂)
    · exact Or.inr (Or.inr ⟨h,h₂⟩)

theorem companion_exponent :
    (1+(23/20:ℝ))*(243/625)-shortWidth = 18023/25000 := by
  norm_num [shortWidth]

theorem companion_length {U X₁ X₂ : ℝ} (hU : 0 < U)
    (hprod : X₁*X₂ ≤ U^((1+(23/20:ℝ))*(243/625))) :
    X₁*X₂/U^shortWidth ≤ U^(18023/25000 : ℝ) := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hU _)).mpr
  rw [←Real.rpow_add hU]
  convert hprod using 1 <;> norm_num [shortWidth]

/-- An exact cutoff check for the genuine first Poisson theorem. This
includes its dyadic collar four and the positive retained-frequency buffer. -/
theorem short_cutoff_of_power {U V K b w H ξ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hvol : V ≤ U^(2*(b+w)))
    (hK : K = U^H) (hcut : 4*U^(4*(b+w)-H+ξ/2) < 1) :
    4*(V^2/K)*U^(ξ/2) < 1 := by
  have hu : 0 < U := zero_lt_one.trans_le hU
  have hk : 0 < K := hK ▸ Real.rpow_pos_of_pos hu H
  have hp : V^2 ≤ (U^(2*(b+w)))^2 := pow_le_pow_left₀ hV hvol 2
  have hle := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hp hk.le) (Real.rpow_nonneg hu.le (ξ/2))
  rw [mul_assoc (4:ℝ)]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 4))
  convert hcut using 1
  rw [hK,←Real.rpow_natCast,←Real.rpow_mul hu.le,←Real.rpow_sub hu,
    ←Real.rpow_add hu]
  congr 2
  ring

/-- Every strict P.3 conductor reserve admits an early positive frequency
buffer, with an ambient threshold independent of the live coefficients. -/
theorem eventually_short_cutoff {b w H ξ : ℝ}
    (hreserve : 4*(b+w)+ξ/2 < H) :
    ∀ᶠ U : ℝ in atTop, 1 ≤ U ∧ 4*U^(4*(b+w)-H+ξ/2) < 1 := by
  let δ := H-4*(b+w)-ξ/2
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hreserve]
  have he := (tendsto_rpow_atTop hδ).eventually (eventually_gt_atTop (4:ℝ))
  filter_upwards [he,eventually_ge_atTop (1:ℝ)] with U hpow hU
  refine ⟨hU,?_⟩
  have hu : 0 < U := zero_lt_one.trans_le hU
  have hp := Real.rpow_pos_of_pos hu δ
  have hexp : 4*(b+w)-H+ξ/2 = -δ := by dsimp [δ]; ring
  rw [hexp,Real.rpow_neg hu.le,←div_eq_mul_inv]
  exact (div_lt_one hp).mpr hpow

#print axioms short_cutoff_of_power
#print axioms companion_length
#print axioms eventually_short_cutoff
end
end QRH.Cycle092.ReferenceShortP3
