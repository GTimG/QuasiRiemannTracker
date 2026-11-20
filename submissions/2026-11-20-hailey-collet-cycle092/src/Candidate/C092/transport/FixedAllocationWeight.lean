/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed-row squared amplitude pays the complete common and Möbius divisor
norms. This includes shortened lengths below one. -/
import Candidate.C092.transport.CofactorPairBudget
set_option autoImplicit false
namespace QRH.Cycle092.FixedAllocationWeight
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
local notation "O" => HeckeFamily.O

theorem squared_cancellation {q q₀ L : ℝ} (hq₀ : 1 ≤ q₀) (hq : q₀ ≤ q) :
    q⁻¹^2 * (max 1 (L/q))^(-(6/5):ℝ) ≤ (q₀*max 1 L)⁻¹ := by
  have hq1 := hq₀.trans hq
  have hqp := zero_lt_one.trans_le hq1
  have hq₀p := zero_lt_one.trans_le hq₀
  let X := max 1 (L/q)
  have hx : 1 ≤ X := le_max_left _ _
  have hxp := zero_lt_one.trans_le hx
  have hL : L ≤ q*X := by
    have := (div_le_iff₀ hqp).mp (le_max_right 1 (L/q)); dsimp only [X]; linarith
  have hm : max 1 L ≤ q*X := max_le (one_le_mul_of_one_le_of_one_le hq1 hx) hL
  have hh : X ≤ X^(6/5:ℝ) := by
    calc
      _ = X^(1:ℝ) := (Real.rpow_one X).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hden : q₀*max 1 L ≤ q^2*X^(6/5:ℝ) := by
    calc
      _ ≤ q*(q*X) := mul_le_mul hq hm (zero_le_one.trans (le_max_left _ _)) hqp.le
      _ ≤ _ := by rw [←mul_assoc,←pow_two]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)
  change q⁻¹^2 * X^(-(6/5):ℝ) ≤ _
  rw [Real.rpow_neg hxp.le,inv_pow,←mul_inv]
  exact inv_le_inv₀ (by positivity) (mul_pos hq₀p (zero_lt_one.trans_le (le_max_left _ _))) |>.mpr hden

theorem concrete_primary_norms {ι : Type*} [Fintype ι] (B C : ι → Ideal O)
    (d₁ d₂ G E : Ideal O) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hG : G ≠ 0) (hE : E ≠ 0) (hc : ∀ j, C j ≠ 0) (hg : ∏ j, B j = G)
    (hdiv : E ∣ ∏ j, C j) :
    let pd : ℝ := (d₁.absNorm:ℝ)*d₂.absNorm
    1 ≤ pd*G.absNorm*E.absNorm ∧ pd*G.absNorm*E.absNorm ≤
      pd*(∏ j, ((B j*C j).absNorm:ℝ)) := by
  dsimp only
  have hN (I : Ideal O) (hh : I ≠ 0) : 1 ≤ (I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hh)
  have hp : 1 ≤ (d₁.absNorm:ℝ)*d₂.absNorm := one_le_mul_of_one_le_of_one_le (hN _ hd₁) (hN _ hd₂)
  refine ⟨one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp (hN _ hG)) (hN _ hE),?_⟩
  have hP : (∏ j, C j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)
  have hh : (E.absNorm:ℝ) ≤ (∏ j,C j).absNorm := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)) (map_dvd Ideal.absNorm hdiv)
  have hprod : (∏ j, ((B j*C j).absNorm:ℝ)) = (G.absNorm:ℝ)*(∏ j, C j).absNorm := by
    rw [←hg]; simp only [map_mul,map_prod,Nat.cast_mul,Nat.cast_prod,Finset.prod_mul_distrib]
  rw [hprod,←mul_assoc]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

theorem actual_squared_weight {ι : Type*} [Fintype ι] (B C : ι → Ideal O)
    (d₁ d₂ G E : Ideal O) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hG : G ≠ 0) (hE : E ≠ 0) (hc : ∀ j, C j ≠ 0) (hg : ∏ j,B j=G)
    (hdiv : E ∣ ∏ j,C j) (L : ℝ) :
    let pd : ℝ := (d₁.absNorm:ℝ)*d₂.absNorm
    let q := pd*(∏ j,((B j*C j).absNorm:ℝ))
    q⁻¹^2 * (max 1 (L/q))^(-(6/5):ℝ) ≤ (pd*G.absNorm*E.absNorm*max 1 L)⁻¹ := by
  have hh := concrete_primary_norms B C d₁ d₂ G E hd₁ hd₂ hG hE hc hg hdiv
  exact squared_cancellation hh.1 hh.2

#print axioms actual_squared_weight
end
end QRH.Cycle092.FixedAllocationWeight
