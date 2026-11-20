/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Whole-slot Gauss selection followed by the actual second Poisson. -/
import Candidate.C092.transport.RawSidesAllocation

set_option autoImplicit false
namespace QRH.Cycle092.RawSides
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentChildRows CenteredMomentSourceRow
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- Whole selected slots, their actual fourth-power row dilation and exact
    seed-preimage count, followed by second Poisson on the whole residual
    coefficient. All four child bounds concern literal physical terms. -/
theorem selected_residual_of_terms (s : Source ι a b)
    (hB1 : ∀ k : ι ⊕ Fin 2, s.B k = 1) (J : Finset ι) (ha : 0 < a)
    (Us V : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (himg : ∀ u ∈ Us, ∀ y ∈ selY s J, seedRest u (∏ j, y j) ∈ V)
    (hV : CompleteSeeds (restSource s hB1 J) ha V)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) (Kp : (J → Id) → ℝ)
    (hK : 0 < K) (hKp : ∀ y ∈ selY s J, 0 < Kp y)
    (hKK : ∀ y ∈ selY s J,
      2*K*‖ConcreteTraceCRT.eisEmbedding (CompletedGauss.primaryGenerator (∏ j, y j)^4)‖^2 ≤ Kp y)
    (hH : ∀ I ∈ sourceColumns (restSource s hB1 J),
      sourceCoefficient (restSource s hB1 J) ha 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H)
    (E₀ Ef Et Er : (J → Id) → RayCharacter → ℝ)
    (hz : ∀ y ∈ selY s J, ∀ ζ,
      zeroTerms (restSource s hB1 J) ha V (childCharacter τ ζ) t (Kp y) ≤ E₀ y ζ)
    (hf : ∀ y ∈ selY s J, ∀ ζ,
      fixedTerms (restSource s hB1 J) ha V (childCharacter τ ζ) χ₀ Q m t (Kp y) Tsec Z ξ H ≤ Ef y ζ)
    (ht : ∀ y ∈ selY s J, ∀ ζ,
      tailTerms (restSource s hB1 J) ha V (childCharacter τ ζ) t (Kp y) Tsec Z ξ ≤ Et y ζ)
    (hr : ∀ y ∈ selY s J, ∀ ζ,
      regularTerms (restSource s hB1 J) ha (childCharacter τ ζ) χ₀ Q m t (Kp y) Tsec Z ξ H ≤ Er y ζ) :
    ∑ u ∈ Us, Qenergy s ha u τ t K ≤
      Atot s J τ t * ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ζ : RayCharacter,
        (2 : ℝ)^(IdealMobiusDivisorSum.primeSupport (∏ j, y j)).card *
          (E₀ y ζ + Ef y ζ + Et y ζ + Er y ζ) := by
  refine (summed_live_energy_le s hB1 J ha Us V hUs himg τ t K Kp hK hKp hKK).trans ?_
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ Atot s J τ t by unfold Atot; positivity)
  apply Finset.sum_le_sum
  intro y hy
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum
  intro ζ _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact residual_of_terms (restSource s hB1 J) ha V hV (childCharacter τ ζ) χ₀ Q m
    t (Kp y) Tsec Z ξ H (E₀ y ζ) (Ef y ζ) (Et y ζ) (Er y ζ)
    (hKp y hy) hH (hz y hy ζ) (hf y hy ζ) (ht y hy ζ) (hr y hy ζ)

#print axioms selected_residual_of_terms
end
end QRH.Cycle092.RawSides
