/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Generalizes the checked Cycle61 restricted-kernel transport to explicit row selectors.
The finite coefficient, divisor mask and actual positive energy are retained. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondScaled
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RestrictedEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.Record1252270103GlobalSelected
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentSecondScaled CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem whole_kernel_selected_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (keep : RayCharacter→O→Prop),
      (∀ χ : RayCharacter, ∀ z∈rows, keep χ z) →
      (∀ χ : RayCharacter, ∀ z∈rows, keep χ (-z)) →
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (keep χ) S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K) ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (keep ξ) T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K) ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_restricted_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x keep hkeep₁ hkeep₂ hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z))
    (keep χ) (keep (ξ⁻¹))
    (hkeep₁ χ) (hkeep₂ (ξ⁻¹)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.Record1252270103GlobalSelected

end

end OAI

#print axioms OAI.SevenEighths.Record1252270103GlobalSelected.whole_kernel_selected_second_bound
