/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.InitialMoment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionary

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy
open CenteredMomentSecondHeightFamily CenteredMomentLattice
open CenteredMomentInductionEnergy CenteredMomentPositiveSummability
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot CenteredMomentEnergyBands
open QRH.Record12518109Source
local notation "O" => HeckeFamily.O

/-- Exact full-product normalization at a common height. The relative-slot
coefficients retain their height phase, while the two plain profiles carry
the same height. Only unit-modulus scalar phases disappear on taking norms. -/
theorem natural_initial_product_norm {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b)
    (pool : α → Finset (Ideal O)) (β : α → Ideal O → ℂ) (P : α → ℝ)
    (hP : ∀ i, 0 < P i) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ‖positiveSlotRow η (fixedBadMask * idealGenerator 1) 1 z W₁ W₂ pool β P t X₁ X₂‖ =
      ‖polynomial F.character false
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t) X₁ 0 0 *
        polynomial F.character false
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) X₂ 0 0 *
        ∏ i, naturalSlot F.character (pool i) (heightCoefficient (β i) t) (P i)‖ := by
  have h := congrArg (fun x : ℂ => ‖x‖) (original_positive_normalized F 1 one_ne_zero
    W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
    pool β P hP t X₁ X₂ hX₁ hX₂)
  have he (I : Ideal O) : idealCoeff (excluded F.character 1) I =
      idealCoeff F.character I := by
    rw [excluded_ideal _ _ one_ne_zero]
    simp only [isCoprime_one_right, ite_true]
  have hpoly := HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff
    (excluded F.character 1) F.character he
  simp_rw [hpoly] at h
  have hslot (i : α) : naturalSlot (excluded F.character 1) (pool i)
      (heightCoefficient (β i) t) (P i) =
      naturalSlot F.character (pool i) (heightCoefficient (β i) t) (P i) := by
    simp only [naturalSlot, he]
  simp_rw [hslot] at h
  simpa only [norm_mul, positive_height_phase_norm _ _ hX₁,
    positive_height_phase_norm _ _ hX₂, one_mul] using h

/-- A finite collection of kept rows is bounded by the literal full radial
energy whenever its radial profile majorizes one on those rows. -/
theorem finite_positive_le_energy {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (m A : O) (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ)
    (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a b)
    (pool : α → Finset (Ideal O)) (β : α → Ideal O → ℂ) (P : α → ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep z)
    (hcover : ∀ z ∈ rows, 1 ≤ (Φ (‖eisEmbedding z‖^2 / K)).re) :
    (∑ z ∈ rows, ‖positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂‖^2) ≤
      energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K := by
  obtain ⟨D, hD⟩ := product_bounded η m A t
    (Real.sqrt (X₁ * X₂ * ∏ i, P i) : ℂ)⁻¹ W₁ W₂ b b X₁ X₂
    (fun _ hx => (hs₁ hx).2) (fun _ hx => (hs₂ hx).2) hX₁ hX₂ pool β
  have hsum := bounded_radial_summable
    (fun z => positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂) D hD keep Φ K hK
  apply le_trans (Finset.sum_le_sum (fun z hz => ?_))
    (hsum.sum_le_tsum rows (fun z _ => ?_))
  · rw [ite_eq_left (hkeep z hz)]
    exact le_mul_of_one_le_right (sq_nonneg _) (hcover z hz)
  · split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

omit [Fintype α] in
/-- A previous actual initial source supplies a finite raw-row moment with
the same relative slot dictionary, both heights, initialKeep, common smooth
profiles and whole-product normalization. This is an implication from the
previous source theorem; it introduces no substitute analytic assumption. -/
theorem initialAffineAt_finite_canonical
    (face : SourceFace) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ) (ha : 0 < a) (hZ : 0 < Z)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (hsource : InitialAffineAt (α:=α) rayModulus H hH face W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree S C)
    (T : Finset α) (θ : T → RayQuotient.Characters rayModulus H)
    (w σ v : T → ℝ) (t height : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hσlo : ∀ i, σlo ≤ σ i) (hσhi : ∀ i, σ i ≤ σhi)
    (hheight : 0 ≤ height) (hv : ∀ i, |v i| ≤ height)
    (M : ℝ) (hMlo : Mmin ≤ M) (hMhi : M ≤ Mmax)
    (Φ : 𝓢(ℝ,ℂ)) (hΦsupport : Function.support (Φ : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (hΦ : ∀ x, 0 ≤ (Φ x).re)
    (p : Profiles a b) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hadmit : face.Admissible (length Z X₁) (length Z X₂) (∑ i, w i) M)
    (rows : Finset O) (hkeep : ∀ z ∈ rows, initialKeep η (internalQ Q η₀) z)
    (hcover : ∀ z ∈ rows, 1 ≤ (Φ (‖eisEmbedding z‖^2 / Z^M)).re)
    (F : ∀ z : rows, NaturalRow η z.val) :
    (∑ z : rows, ‖polynomial (F z).character false
        (normPowerProfile (p.profile 0) a b ha (p.support 0) ((p.profile 0).smooth ⊤) t) X₁ 0 0 *
      polynomial (F z).character false
        (normPowerProfile (p.profile 1) a b ha (p.support 1) ((p.profile 1).smooth ⊤) t) X₂ 0 0 *
      ∏ i : T, naturalSlot (F z).character (primePool rayModulus H bslot (Z^(w i)))
        (heightCoefficient (fun I => idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2) ≤
      C * QuadraticInitialBound.diagonalControl Φ * (p.control S)^2 *
        (1 + |t| + height)^degree * Z^(M + ε) := by
  have he := hsource T θ w σ v t height hw hwm hσlo hσhi hheight hv
    M hMlo hMhi Φ hΦsupport hΦ p X₁ X₂ hX₁ hX₂ hadmit
  have hp := finite_positive_le_energy η (fixedBadMask * idealGenerator 1) 1
    (p.profile 0) (p.profile 1) a b (p.support 0) (p.support 1)
    (fun i : T => primePool rayModulus H bslot (Z^(w i)))
    (fun (i : T) I => idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i : T => Z^(w i)) t X₁ X₂ hX₁ hX₂ (initialKeep η (internalQ Q η₀))
    Φ (Z^M) (Real.rpow_pos_of_pos hZ _) hΦ rows hkeep hcover
  apply le_trans ?_ (hp.trans he)
  rw [← Finset.sum_coe_sort rows]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg (fun u : ℝ => u^2)
    (natural_initial_product_norm (F z) (p.profile 0) (p.profile 1) a b ha
      (p.support 0) (p.support 1) _ _ _ (fun _ => Real.rpow_pos_of_pos hZ _)
      t X₁ X₂ hX₁ hX₂).symm

end
end OAI.SevenEighths.Record12518109Raw

#print axioms OAI.SevenEighths.Record12518109Raw.natural_initial_product_norm
#print axioms OAI.SevenEighths.Record12518109Raw.finite_positive_le_energy
#print axioms OAI.SevenEighths.Record12518109Raw.initialAffineAt_finite_canonical
