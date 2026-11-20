/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Apply the fixed-inducing H8 estimate to the two genuinely shortened
rectangles with their own phases, then return to the original normalizer. -/
import Candidate.C092.transport.FixedCubeApplication
import Candidate.C092.transport.FixedAllocationWeight
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
namespace QRH.Cycle092.FixedAllocationWeight
open QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O

theorem restore_normalization {a : ℂ} {T q q₀ L C : ℝ} (hT : 0<T) (hq₀ : 1≤q₀)
    (hq : q₀≤q) (hC : 0≤C)
    (ha : ‖(Real.sqrt (T/q):ℂ)⁻¹*a‖ ≤ C*Real.sqrt (T/q)*(max 1 (L/q))^(-(3/5):ℝ)) :
    ‖(Real.sqrt T:ℂ)⁻¹*a‖^2 ≤ C^2*T*(q₀*max 1 L)⁻¹ := by
  have hq' := zero_lt_one.trans_le (hq₀.trans hq)
  have hx := div_pos hT hq'
  let m := max (1:ℝ) (L/q)
  have hm : 0 < m := zero_lt_one.trans_le (le_max_left _ _)
  have hS := Real.sqrt_pos.mpr hx
  have hraw : ‖a‖ ≤ C*(T/q)*m^(-(3/5):ℝ) := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hS.le,←div_eq_inv_mul] at ha
    have h := (div_le_iff₀ hS).mp ha
    refine h.trans_eq ?_
    calc
      _ = C*(Real.sqrt (T/q))^2*m^(-(3/5):ℝ) := by dsimp only [m]; ring
      _ = _ := by rw [Real.sq_sqrt hx.le]
  have hpow : (m^(-(3/5):ℝ))^2=m^(-(6/5):ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hm.le]
    norm_num
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hT]
  calc
    _ ≤ (C*(T/q)*m^(-(3/5):ℝ))^2/T :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hraw 2) hT.le
    _ = C^2*T*(q⁻¹^2*m^(-(6/5):ℝ)) := by rw [mul_pow,hpow]; field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (squared_cancellation hq₀ hq) (mul_nonneg (sq_nonneg C) hT.le)

theorem fixed_shortened_square (P₁ P₂ : OrdinaryProfile) (ε B : ℝ)
    (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∀ Q₁ Q₂ : Ideal O, ∃ C : ℝ, 0<C ∧
    ∀ (D₁ D₂ : FixedCubeDatum), D₁.Q=Q₁ → D₂.Q=Q₂ →
    ∀ (labels supplying holes₁ holes₂ : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
    supplying ∪ holes₁ ∪ holes₂ ⊆ labels →
    (∀ p ∈ fixedCubeBad D₁ D₂ labels, allowed p ⊆ supplyingResidualPairs D₁.row D₂.row supplying holes₁ holes₂ p) →
    ∀ U : ℝ, 1≤U →
      (HeckeRowClosure.rowConductorBound D₁.η D₁.m 1 (D₁.A*D₁.z):ℝ) ≤ U^B →
      (HeckeRowClosure.rowConductorBound D₂.η D₂.m 1 (D₂.A*D₂.z):ℝ) ≤ U^B →
      ((∏ p ∈ labels, p.val).absNorm:ℝ) ≤ U^B →
    ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ T L q q₀ : ℝ, 0<T → 0<L → 1≤q₀ → q₀≤q →
      L/q ≤ X₁ → L/q ≤ X₂ → L/q ≤ Y₁ → L/q ≤ Y₂ →
      X₁*X₂=T/q → Y₁*Y₂=T/q →
      let V₁ := P₁.atHeight t₁
      let V₂ := P₂.atHeight t₂
      let arm := fun x y => (fixedCubeOutsidePhase V₁ V₂ x y)⁻¹*
        fixedCubeRawSource D₁ D₂ V₁ V₂ (fixedCubeBad D₁ D₂ labels) allowed x y
      ‖(Real.sqrt T:ℂ)⁻¹*(arm X₁ X₂-arm Y₁ Y₂)‖^2 ≤
        (C*U^ε*(1+‖t₁‖+‖t₂‖)^J)^2*T*(q₀*max 1 L)⁻¹ := by
  obtain ⟨J,hJ⟩ := fixedCubeRawSource_uniform P₁ P₂ ε B hε hB
  refine ⟨J,?_⟩;intro Q₁ Q₂
  obtain ⟨C,hC,hsrc⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩;intro D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hsub hall U hU hD₁ hD₂ hprod
  intro t₁ t₂ X₁ X₂ Y₁ Y₂ T L q q₀ hT hL hq₀ hq hx₁ hx₂ hy₁ hy₂ heq heq'
  have hUp := zero_lt_one.trans_le hU
  exact restore_normalization hT hq₀ hq (by positivity)
    (hsrc D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hsub hall U hU hD₁ hD₂ hprod
      t₁ t₂ X₁ X₂ Y₁ Y₂ (T/q) (L/q) (div_pos hL (zero_lt_one.trans_le (hq₀.trans hq)))
      hx₁ hx₂ hy₁ hy₂ heq heq')

#print axioms fixed_shortened_square
end QRH.Cycle092.FixedAllocationWeight
