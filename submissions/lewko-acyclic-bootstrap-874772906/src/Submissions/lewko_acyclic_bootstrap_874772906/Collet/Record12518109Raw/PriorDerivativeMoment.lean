/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.InitialMoment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentEnergyProfiles CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentInductionEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentEnergyBands
open CenteredMomentSecondHeightFamily
open QRH.Record12518109Source
local notation "O" => HeckeFamily.O

/-- The two common scale derivatives as an actual original-source profile pair. -/
def derivativeProfiles {a b : ℝ} (W₁ W₂ : 𝓢(ℝ,ℂ))
    (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b) (j k : Fin 2) : Profiles a b where
  profile := fun i => if i = 0 then derivativeChoice W₁ j else derivativeChoice W₂ k
  support := by
    intro i
    split_ifs
    · exact derivativeChoice_support _ _ _ hs₁ j
    · exact derivativeChoice_support _ _ _ hs₂ k

/-- The seminorm loss for either scale derivative is uniform before the profiles,
slot family, moving puncture and all quotient scales. -/
theorem derivativeProfiles_control (S : Finset (ℕ×ℕ)) :
    ∃ T : Finset (ℕ×ℕ), ∃ D : ℝ, 0 < D ∧
    ∀ {a b : ℝ} (W₁ W₂ : 𝓢(ℝ,ℂ))
      (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
      (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b) (j k : Fin 2),
      (derivativeProfiles W₁ W₂ hs₁ hs₂ j k).control S ≤
        D * (sourceControl T W₁ * sourceControl T W₂) := by
  obtain ⟨T,D,hD,hd⟩ := derivative_choice_control S
  refine ⟨T,D^2,sq_pos_of_pos hD,?_⟩
  intro a b W₁ W₂ hs₁ hs₂ j k
  simp only [Profiles.control,derivativeProfiles,ite_true,show (1 : Fin 2) ≠ 0 by decide,ite_false]
  apply (mul_le_mul (hd W₁ j) (hd W₂ k) (sourceControl_nonneg _ _)
    (mul_nonneg hD.le (sourceControl_nonneg _ _))).trans_eq
  ring

variable {α : Type*} [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

/-- Each shortened/deleted branch admitted by the previous face is bounded by
that literal source theorem. The common derivative seminorm and inherited
relative height are retained explicitly. This is the prior branch of R17. -/
theorem initialAffineAt_derivative_branch
    (face : SourceFace) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ) (hZ : 0 < Z)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ))
    (C : ℝ) (hC : 0 ≤ C)
    (hsource : InitialAffineAt (α:=α) rayModulus H hH face W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree S C) :
    ∃ T : Finset (ℕ×ℕ), ∃ D : ℝ, 0 < D ∧
    ∀ (F : Finset α) (θ : α → RayQuotient.Characters rayModulus H)
      (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i ∈ F, 0 ≤ w i) → (∀ i ∈ F, w i ≤ mesh) →
      (∀ i ∈ F, σlo ≤ σ i) → (∀ i ∈ F, σ i ≤ σhi) →
      0 ≤ height → (∀ i ∈ F, |freq i| ≤ height) →
    ∀ (J : Finset α) (M : ℝ), Mmin ≤ M → M ≤ Mmax →
    ∀ (Φ : 𝓢(ℝ,ℂ)), Function.support (Φ : ℝ→ℂ) ⊆ Set.Iic bΦ →
      (∀ x, 0 ≤ (Φ x).re) →
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ))
      (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
      (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b)
      (j k : Fin 2) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      face.Admissible (length Z X₁) (length Z X₂) (∑ i ∈ F \ J, w i) M →
      energy η (fixedBadMask*idealGenerator 1) 1 0
        (derivativeChoice W₁ j) (derivativeChoice W₂ k)
        (fun i : ↥(F \ J) => primePool rayModulus H bslot (Z^(w i)))
        (fun (i : ↥(F \ J)) I =>
          idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (t+freq i) I)
        (fun i : ↥(F \ J) => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C * QuadraticInitialBound.diagonalControl Φ *
        (D * (sourceControl T W₁ * sourceControl T W₂))^2 *
        (1+|t|+height)^degree * Z^(M+ε) := by
  obtain ⟨T,D,hD,hd⟩ := derivativeProfiles_control S
  refine ⟨T,D,hD,?_⟩
  intro F θ w σ freq t height hw hwm hσlo hσhi hheight hv J M hMlo hMhi
    Φ hΦsupport hΦ W₁ W₂ hs₁ hs₂ j k X₁ X₂ hX₁ hX₂ hadmit
  let p := derivativeProfiles W₁ W₂ hs₁ hs₂ j k
  have he := hsource (F \ J) (fun i => θ i) (fun i => w i) (fun i => σ i)
    (fun i => t+freq i) 0 (|t|+height)
    (fun i => hw i (Finset.mem_sdiff.mp i.property).1)
    (fun i => hwm i (Finset.mem_sdiff.mp i.property).1)
    (fun i => hσlo i (Finset.mem_sdiff.mp i.property).1)
    (fun i => hσhi i (Finset.mem_sdiff.mp i.property).1)
    (add_nonneg (abs_nonneg _) hheight)
    (fun i => (abs_add_le t (freq i)).trans
      (add_le_add (le_refl |t|) (hv i (Finset.mem_sdiff.mp i.property).1)))
    M hMlo hMhi Φ hΦsupport hΦ p X₁ X₂ hX₁ hX₂
    (by simpa only [Finset.sum_coe_sort] using hadmit)
  have hp : p.control S ≤ D * (sourceControl T W₁ * sourceControl T W₂) :=
    hd W₁ W₂ hs₁ hs₂ j k
  have hmono := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (p.control_nonneg S) hp 2)
        (mul_nonneg hC (QuadraticInitialBound.diagonalControl_nonneg Φ)))
      (pow_nonneg (by positivity : 0 ≤ 1+|t|+height) degree))
    (Real.rpow_nonneg hZ.le (M+ε))
  apply le_trans ?_ hmono
  simpa only [p,derivativeProfiles,ite_true,show (1 : Fin 2) ≠ 0 by decide,ite_false,
    abs_zero,add_zero,add_assoc] using he

end
end OAI.SevenEighths.Record12518109Raw

#print axioms OAI.SevenEighths.Record12518109Raw.derivativeProfiles_control
#print axioms OAI.SevenEighths.Record12518109Raw.initialAffineAt_derivative_branch
