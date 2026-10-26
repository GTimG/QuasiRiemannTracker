/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.NaturalDerivativeMoment

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentInductionEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentEnergyBands
open QRH.Record12518109Source Record12518109Natural.InitialNatural
local notation "O" => HeckeFamily.O
variable {α : Type*} [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

/-- R17 with its analytic suppliers: every simultaneous plain shortening and
slot deletion is bounded by the checked previous initial source or the genuine
natural initial source. Both budgets are uniform over scale derivatives; the
same original relative-slot dictionary and initialKeep remain in the energy. -/
theorem initial_sources_derivative_dispatch
    (face : SourceFace) (Kcap : ℝ) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ) (hZ : 0 < Z)
    (η η₀ : Character) (Q : Ideal O)
    (degreeP degreeN : ℕ) (SP SN : Finset (ℕ×ℕ))
    (CP CN : ℝ) (hCP : 0 ≤ CP) (hCN : 0 ≤ CN)
    (hprior : InitialAffineAt (α:=α) rayModulus H hH face W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degreeP SP CP)
    (hnatural : InitialNaturalAt (α:=α) rayModulus H hH Kcap W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degreeN SN CN) :
    ∃ TP : Finset (ℕ×ℕ), ∃ DP : ℝ, ∃ TN : Finset (ℕ×ℕ), ∃ DN : ℝ,
      0 < DP ∧ 0 < DN ∧
    ∀ (F : Finset α) (θ : α → RayQuotient.Characters rayModulus H)
      (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i ∈ F, 0 ≤ w i) → (∀ i ∈ F, w i ≤ mesh) →
      (∀ i ∈ F, σlo ≤ σ i) → (∀ i ∈ F, σ i ≤ σhi) →
      0 ≤ height → (∀ i ∈ F, |freq i| ≤ height) →
    ∀ (J : Finset α) (M m₁ m₂ cap : ℝ), Mmin ≤ M → M ≤ Mmax →
      DownwardCaps face Kcap m₁ m₂ cap M →
    ∀ (Φ : 𝓢(ℝ,ℂ)), Function.support (Φ : ℝ→ℂ) ⊆ Set.Iic bΦ →
      (∀ x, 0 ≤ (Φ x).re) →
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ))
      (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
      (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b)
      (j k : Fin 2) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      length Z X₁ ≤ m₁ → length Z X₂ ≤ m₂ → (∑ i ∈ F \ J, w i) ≤ cap →
      energy η (fixedBadMask*idealGenerator 1) 1 0
        (derivativeChoice W₁ j) (derivativeChoice W₂ k)
        (fun i : ↥(F \ J) => primePool rayModulus H bslot (Z^(w i)))
        (fun (i : ↥(F \ J)) I =>
          idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (t+freq i) I)
        (fun i : ↥(F \ J) => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      CP * QuadraticInitialBound.diagonalControl Φ *
        (DP * (sourceControl TP W₁ * sourceControl TP W₂))^2 *
        (1+|t|+height)^degreeP * Z^(M+ε) +
      CN * QuadraticInitialBound.diagonalControl Φ *
        (DN * (sourceControl TN W₁ * sourceControl TN W₂))^2 *
        (1+|t|+height)^degreeN * Z^(M+ε) := by
  obtain ⟨TP,DP,hDP,hp⟩ := initialAffineAt_derivative_branch rayModulus H hH face W
    bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z hZ η η₀ Q degreeP SP CP hCP hprior
  obtain ⟨TN,DN,hDN,hn⟩ := initialNaturalAt_derivative_branch rayModulus H hH Kcap W
    bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z hZ η η₀ Q degreeN SN CN hCN hnatural
  refine ⟨TP,DP,TN,DN,hDP,hDN,?_⟩
  intro F θ w σ freq t height hw hwm hσlo hσhi hh hv J M m₁ m₂ cap hMlo hMhi hcaps
    Φ hΦs hΦ W₁ W₂ hs₁ hs₂ j k X₁ X₂ hX₁ hX₂ hm₁ hm₂ hcap
  have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
  rcases downward_completion hcaps hm₁ hm₂ hcap with ha | ha
  · have he := hp F θ w σ freq t height hw hwm hσlo hσhi hh hv J M hMlo hMhi
      Φ hΦs hΦ W₁ W₂ hs₁ hs₂ j k X₁ X₂ hX₁ hX₂ ha
    exact he.trans (le_add_of_nonneg_right (by positivity))
  · have he := hn F θ w σ freq t height hw hwm hσlo hσhi hh hv J M hMlo hMhi
      Φ hΦs hΦ W₁ W₂ hs₁ hs₂ j k X₁ X₂ hX₁ hX₂ ha
    exact he.trans (le_add_of_nonneg_left (by positivity))

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.initial_sources_derivative_dispatch
