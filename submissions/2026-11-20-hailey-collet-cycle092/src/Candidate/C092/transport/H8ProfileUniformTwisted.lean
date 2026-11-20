/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Profile-uniform H13 square for independent fixed ordinary-column ray twists. -/
import Candidate.C092.transport.H8ProfileUniformSquared
import Candidate.C092.transport.FixedIndependentTwists
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional
namespace QRH.Cycle092.FixedAllocationWeight
open QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O
theorem fixed_independent_square_homogeneous (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (ω₁ ω₂ : Character) (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ hS : (0,0)∈S,
    ∀ Q₁ Q₂ : Ideal O, ∃ C : ℝ, 0<C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
    ∀ hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc a b,
    ∀ hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc a b,
    ∀ (D₁ D₂ : FixedCubeDatum), D₁.Q=Q₁ → D₂.Q=Q₂ →
    ∀ (labels supplying holes₁ holes₂ : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
    supplying ∪ holes₁ ∪ holes₂ ⊆ labels →
    (∀ p ∈ fixedCubeBad (D₁.twistColumn ω₁) (D₂.twistColumn ω₂) labels, allowed p ⊆ supplyingResidualPairs (D₁.twistColumn ω₁).row (D₂.twistColumn ω₂).row supplying holes₁ holes₂ p) →
      (HeckeRowClosure.rowConductorBound D₁.η D₁.m 1 (D₁.A*D₁.z):ℝ) ≤ U^B →
      (HeckeRowClosure.rowConductorBound D₂.η D₂.m 1 (D₂.A*D₂.z):ℝ) ≤ U^B →
      ((∏ p ∈ labels, p.val).absNorm:ℝ) ≤ U^B →
    ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ T L q q₀ : ℝ, 0<T → 0<L → 1≤q₀ → q₀≤q →
      L/q ≤ X₁ → L/q ≤ X₂ → L/q ≤ Y₁ → L/q ≤ Y₂ →
      X₁*X₂=T/q → Y₁*Y₂=T/q →
      let V₁ := (h8Profile S hS ha hb W₁ hs₁).atHeight t₁
      let V₂ := (h8Profile S hS ha hb W₂ hs₂).atHeight t₂
      let arm := fun x y => (fixedCubeOutsidePhase V₁ V₂ x y)⁻¹*
        fixedCubeRawSource (D₁.twistColumn ω₁) (D₂.twistColumn ω₂) V₁ V₂ (fixedCubeBad (D₁.twistColumn ω₁) (D₂.twistColumn ω₂) labels) allowed x y
      ‖(Real.sqrt T:ℂ)⁻¹*(arm X₁ X₂-arm Y₁ Y₂)‖^2 ≤
        (C*(sourceControl S W₁*sourceControl S W₂)*U^ε*(1+‖t₁‖+‖t₂‖)^J)^2*T*(q₀*max 1 L)⁻¹ := by
  obtain ⟨J,S,hS,hJ⟩ := fixed_shortened_square_homogeneous a b ε (B+1) ha hb hε (by linarith)
  refine ⟨J,S,hS,?_⟩; intro Q₁ Q₂
  obtain ⟨C,hC,hsrc⟩ := hJ (Q₁ ⊓ ω₁.modulus) (Q₂ ⊓ ω₂.modulus)
  refine ⟨C,hC,?_⟩
  filter_upwards [uniform_twist_conductor ω₁ B 1 (by norm_num),uniform_twist_conductor ω₂ B 1 (by norm_num)] with U h₁ h₂
  intro W₁ W₂ hs₁ hs₂ D₁ D₂ hQ₁ hQ₂ labels supplying holes₁ holes₂ allowed hsub hall hD₁ hD₂ hprod
  have hh := hsrc W₁ W₂ hs₁ hs₂ (D₁.twistColumn ω₁) (D₂.twistColumn ω₂) (by change D₁.Q ⊓ ω₁.modulus = _; rw [hQ₁])
    (by change D₂.Q ⊓ ω₂.modulus = _; rw [hQ₂]) labels supplying holes₁ holes₂ allowed hsub hall U h₁.1
    (h₁.2 D₁ hD₁) (h₂.2 D₂ hD₂)
    (hprod.trans (Real.rpow_le_rpow_of_exponent_le h₁.1 (by linarith : B ≤ B+1)))
  exact hh

#print axioms fixed_independent_square_homogeneous
end QRH.Cycle092.FixedAllocationWeight
