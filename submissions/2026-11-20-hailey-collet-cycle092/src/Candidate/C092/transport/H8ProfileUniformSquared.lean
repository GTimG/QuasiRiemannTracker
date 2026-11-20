/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The homogeneous H8 bound under the original H13 reciprocal normalization. -/
import Candidate.C092.transport.H8ProfileUniformHomogeneous
import Candidate.C092.transport.FixedH8Squared
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional
namespace QRH.Cycle092.FixedAllocationWeight
open QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O
theorem fixed_shortened_square_homogeneous (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b)
    (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ hS : (0,0)∈S,
    ∀ Q₁ Q₂ : Ideal O, ∃ C : ℝ, 0<C ∧
    ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
    ∀ hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc a b,
    ∀ hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc a b,
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
      let V₁ := (h8Profile S hS ha hb W₁ hs₁).atHeight t₁
      let V₂ := (h8Profile S hS ha hb W₂ hs₂).atHeight t₂
      let arm := fun x y => (fixedCubeOutsidePhase V₁ V₂ x y)⁻¹*
        fixedCubeRawSource D₁ D₂ V₁ V₂ (fixedCubeBad D₁ D₂ labels) allowed x y
      ‖(Real.sqrt T:ℂ)⁻¹*(arm X₁ X₂-arm Y₁ Y₂)‖^2 ≤
        (C*(sourceControl S W₁*sourceControl S W₂)*U^ε*(1+‖t₁‖+‖t₂‖)^J)^2*T*(q₀*max 1 L)⁻¹ := by
  obtain ⟨J,S,hS,hJ⟩ := fixedCubeRawSource_homogeneous a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩;intro Q₁ Q₂
  obtain ⟨C,hC,hsrc⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩;intro W₁ W₂ hs₁ hs₂ D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hsub hall U hU hD₁ hD₂ hprod
  intro t₁ t₂ X₁ X₂ Y₁ Y₂ T L q q₀ hT hL hq₀ hq hx₁ hx₂ hy₁ hy₂ heq heq'
  have hUp := zero_lt_one.trans_le hU
  have hc₁ := sourceControl_nonneg S W₁
  have hc₂ := sourceControl_nonneg S W₂
  exact restore_normalization hT hq₀ hq (by positivity)
    (hsrc W₁ W₂ hs₁ hs₂ D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hsub hall U hU hD₁ hD₂ hprod
      t₁ t₂ X₁ X₂ Y₁ Y₂ (T/q) (L/q) (div_pos hL (zero_lt_one.trans_le (hq₀.trans hq)))
      hx₁ hx₂ hy₁ hy₂ heq heq')

#print axioms fixed_shortened_square_homogeneous
end QRH.Cycle092.FixedAllocationWeight
