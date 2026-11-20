/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Entrypoint: uniform live-profile controls on the actual fixed-inducing signed
source and original H13 reciprocal normalization, with independent ray twists. -/
import Candidate.C092.transport.H8ProfileUniformTwisted
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional
namespace QRH.Cycle092.FixedAllocationWeight
open QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O
theorem fixed_independent_profiles_square (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (ω₁ ω₂ : Character) (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ hS : (0,0)∈S,
    ∀ Q₁ Q₂ : Ideal O, ∃ C : ℝ, 0<C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ p : Profiles a b,
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
      let V₁ := (h8Profile S hS ha hb (p.profile 0) (p.support 0)).atHeight t₁
      let V₂ := (h8Profile S hS ha hb (p.profile 1) (p.support 1)).atHeight t₂
      let arm := fun x y => (fixedCubeOutsidePhase V₁ V₂ x y)⁻¹*
        fixedCubeRawSource (D₁.twistColumn ω₁) (D₂.twistColumn ω₂) V₁ V₂ (fixedCubeBad (D₁.twistColumn ω₁) (D₂.twistColumn ω₂) labels) allowed x y
      ‖(Real.sqrt T:ℂ)⁻¹*(arm X₁ X₂-arm Y₁ Y₂)‖^2 ≤
        (C*p.control S*U^ε*(1+‖t₁‖+‖t₂‖)^J)^2*T*(q₀*max 1 L)⁻¹ := by
  obtain ⟨J,S,hS,hbound⟩ := fixed_independent_square_homogeneous a b ha hb ω₁ ω₂ ε B hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q₁ Q₂
  obtain ⟨C,hC,h⟩ := hbound Q₁ Q₂
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with U hU
  intro p
  exact hU (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)

#print axioms fixed_independent_profiles_square
end QRH.Cycle092.FixedAllocationWeight
