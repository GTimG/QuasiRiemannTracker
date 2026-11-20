/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Two-character row adaptation of Sil's common-profile separation.
The original one-column Fourier/profile lemmas and majorants are reused unchanged. -/
import Candidate.C092.transport.GroupedPairProfileRow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.GroupedPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform
open MeasureTheory OAI OAI.SevenEighths
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.OrdinaryColumn
open QRH.SilDensitySplit.CubeFree.Packet
open ProfileSeparation (dilate commonPair commonProfile scale pairCoeff cellCoeff pairMajorant pairWeight
  scale_pos commonPair_profile_zero commonPair_profile_one rowTwistedBound)
local notation "O" => ActualEisensteinCubic.O

theorem prefix_hrep {ρ Λ : Type*} (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (rows : Finset ρ) (labels : ρ → Finset Λ) (z : ρ → O) (vd : Λ → ℝ × ℝ)
    (hvd : ∀ r ∈ rows, ∀ l ∈ labels r,
      (vd l).1 ∈ Set.Icc 0 (Real.log 2) ∧ (vd l).2 ∈ Set.Icc 0 (Real.log 2))
    (sc : Λ → ρ → ℂ) (K : ℝ) (hsc : ∀ r ∈ rows, ∀ l ∈ labels r, ‖sc l r‖ ≤ K)
    (B : Λ → ρ → ℂ)
    (hB : ∀ r ∈ rows, ∀ l ∈ labels r, B l r = sc l r *
      row η₁ η₂ m A₁ A₂ (z r) (dilate W₁ (vd l).1) (dilate W₂ (vd l).2) t₁ t₂ Y₁ Y₂ mark) :
    ∀ r ∈ rows, ∀ l ∈ labels r, ‖B l r‖ ≤
      ∑ e ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), ∫ τ : ℝ × ℝ,
        (K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) *
          ‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ (z r)‖ := by
  intro r hr l hl
  obtain ⟨hv₁, hv₂⟩ := hvd r hr l hl
  rw [hB r hr l hl, norm_mul,
    pair_row_separation W₁ W₂ hs₁ hs₂ (vd l) hv₁ hv₂ η₁ η₂ m A₁ A₂ (z r) mark t₁ t₂ Y₁ Y₂ hY₁ hY₂]
  have hsum : ‖∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
        pairCoeff W₁ W₂ hs₁ hs₂ e (vd l) τ * commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ (z r)‖ ≤
      ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
        pairMajorant W₁ W₂ hs₁ hs₂ e τ * ‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ (z r)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext τ
    rw [norm_mul, ProfileSeparation.pairCoeff_norm]
  have hnn : 0 ≤ ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
      pairMajorant W₁ W₂ hs₁ hs₂ e τ * ‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ (z r)‖ :=
    Finset.sum_nonneg fun e _ => integral_nonneg fun τ =>
      mul_nonneg (ProfileSeparation.pairMajorant_nonneg _ _ _ _ _ _) (norm_nonneg _)
  calc ‖sc l r‖ * _ ≤ K * ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
        pairMajorant W₁ W₂ hs₁ hs₂ e τ * ‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ (z r)‖ :=
        mul_le_mul (hsc r hr l hl) hsum (norm_nonneg _) ((norm_nonneg _).trans (hsc r hr l hl))
    _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [← integral_const_mul]
        congr 1
        funext τ
        ring

/-! ### 8. Integrability of the common coefficients against the majorant (`hMA`, `hMA2`) -/

/-- A τ-independent bound for the common row. -/
def commonRowBound (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (e : Fin 2 × Fin 2) (z : O) : ℝ :=
  ‖(Real.sqrt (scale e.1 * Y₁ * (scale e.2 * Y₂)) : ℂ)⁻¹‖ *
    (rowTwistedBound η₁ m A₁ z e.1 t₁ Y₁ * rowTwistedBound η₂ m A₂ z e.2 t₂ Y₂) * ‖mark z‖

theorem commonRow_norm_le (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (e : Fin 2 × Fin 2) (τ : ℝ × ℝ) (z : O) :
    ‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ z‖ ≤ commonRowBound η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e z := by
  simp only [commonRow, row, commonPair_profile_zero, commonPair_profile_one,
    commonRowBound, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact mul_le_mul (ProfileSeparation.rowTwisted_common_norm_le η₁ m A₁ z e.1 τ.1 t₁ Y₁ hY₁)
    (ProfileSeparation.rowTwisted_common_norm_le η₂ m A₂ z e.2 τ.2 t₂ Y₂ hY₂) (norm_nonneg _)
    ((norm_nonneg _).trans (ProfileSeparation.rowTwisted_common_norm_le η₁ m A₁ z e.1 τ.1 t₁ Y₁ hY₁))

theorem commonRow_continuous (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (e : Fin 2 × Fin 2) (z : O) :
    Continuous (fun τ : ℝ × ℝ => commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ z) := by
  simp only [commonRow, row, commonPair_profile_zero, commonPair_profile_one]
  exact (continuous_const.mul
    (((ProfileSeparation.rowTwisted_common_continuous η₁ m A₁ z e.1 t₁ Y₁ hY₁).comp continuous_fst).mul
      ((ProfileSeparation.rowTwisted_common_continuous η₂ m A₂ z e.2 t₂ Y₂ hY₂).comp continuous_snd))).mul
        continuous_const

/-- `hMA`. -/
theorem majorant_row_integrable (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (K : ℝ)
    (hK : 0 ≤ K) (e : Fin 2 × Fin 2) (z : O) :
    Integrable (fun τ : ℝ × ℝ => (K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) *
      ‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ z‖) (volume : Measure (ℝ × ℝ)) := by
  have hM := (ProfileSeparation.pairMajorant_integrable W₁ W₂ hs₁ hs₂ e).const_mul K
  refine (hM.mul_const (commonRowBound η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e z)).mono' ?_ ?_
  · exact hM.aestronglyMeasurable.mul
      (commonRow_continuous η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ hY₁ hY₂ e z).norm.aestronglyMeasurable
  · filter_upwards with τ
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (mul_nonneg hK (ProfileSeparation.pairMajorant_nonneg _ _ _ _ _ _))]
    exact mul_le_mul_of_nonneg_left (commonRow_norm_le η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ hY₁ hY₂ e τ z)
      (mul_nonneg hK (ProfileSeparation.pairMajorant_nonneg _ _ _ _ _ _))

/-- `hMA2`. -/
theorem majorant_row_sq_integrable (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (K : ℝ)
    (hK : 0 ≤ K) (e : Fin 2 × Fin 2) (z : O) :
    Integrable (fun τ : ℝ × ℝ => (K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) *
      ‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ z‖ ^ 2) (volume : Measure (ℝ × ℝ)) := by
  have hM := (ProfileSeparation.pairMajorant_integrable W₁ W₂ hs₁ hs₂ e).const_mul K
  refine (hM.mul_const (commonRowBound η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e z ^ 2)).mono' ?_ ?_
  · exact hM.aestronglyMeasurable.mul
      ((commonRow_continuous η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ hY₁ hY₂ e z).norm.pow 2).aestronglyMeasurable
  · filter_upwards with τ
    rw [norm_mul, norm_pow, norm_norm,
      Real.norm_of_nonneg (mul_nonneg hK (ProfileSeparation.pairMajorant_nonneg _ _ _ _ _ _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _)
        (commonRow_norm_le η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ hY₁ hY₂ e τ z) 2)
      (mul_nonneg hK (ProfileSeparation.pairMajorant_nonneg _ _ _ _ _ _))

/-- **Common-profile separation for ordinary-prefix dilations.** The weighted packet sum of the
literal prefix-dilated positive slot rows is bounded by the fibre bound `D`, the source bound
`C·pairWeight J·T` for the label-independent common rows, and the two majorant masses. -/
theorem prefix_weighted_separation {ρ Λ : Type*} (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (rows : Finset ρ) (labels : ρ → Finset Λ) (z : ρ → O) (vd : Λ → ℝ × ℝ)
    (hvd : ∀ r ∈ rows, ∀ l ∈ labels r,
      (vd l).1 ∈ Set.Icc 0 (Real.log 2) ∧ (vd l).2 ∈ Set.Icc 0 (Real.log 2))
    (sc : Λ → ρ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hsc : ∀ r ∈ rows, ∀ l ∈ labels r, ‖sc l r‖ ≤ K)
    (B : Λ → ρ → ℂ)
    (hB : ∀ r ∈ rows, ∀ l ∈ labels r, B l r = sc l r *
      row η₁ η₂ m A₁ A₂ (z r) (dilate W₁ (vd l).1) (dilate W₂ (vd l).2) t₁ t₂ Y₁ Y₂ mark)
    (w : Λ → ρ → ℝ) (D C T : ℝ) (J : ℕ)
    (hw : ∀ l r, 0 ≤ w l r) (hD0 : 0 ≤ D) (hD : ∀ r ∈ rows, ∑ l ∈ labels r, w l r ≤ D)
    (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hsource : ∀ (e : Fin 2 × Fin 2) (τ : ℝ × ℝ),
      ∑ r ∈ rows, ‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ (z r)‖ ^ 2 ≤ C * pairWeight J τ * T) :
    ∑ r ∈ rows, ∑ l ∈ labels r, w l r * ‖B l r‖ ^ 2 ≤
      D * C * (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ, K * pairMajorant W₁ W₂ hs₁ hs₂ e τ) *
        (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
          K * pairMajorant W₁ W₂ hs₁ hs₂ e τ * pairWeight J τ) * T :=
  QRH.SilDensitySplit.CommonProfile.weighted_separation (volume : Measure (ℝ × ℝ)) Finset.univ rows labels w B
    (fun e τ => K * pairMajorant W₁ W₂ hs₁ hs₂ e τ)
    (fun e τ r => commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ (z r)) (pairWeight J) D C T
    hw hD0 hD (fun _ _ => mul_nonneg hK (ProfileSeparation.pairMajorant_nonneg _ _ _ _ _ _))
    (ProfileSeparation.pairWeight_nonneg J) hC hT
    (ProfileSeparation.prefix_hM1 W₁ W₂ hs₁ hs₂ K) (ProfileSeparation.prefix_hMω W₁ W₂ hs₁ hs₂ K J)
    (fun e _ r _ => majorant_row_integrable W₁ W₂ hs₁ hs₂ η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ hY₁ hY₂ K hK e (z r))
    (fun e _ r _ =>
      majorant_row_sq_integrable W₁ W₂ hs₁ hs₂ η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ hY₁ hY₂ K hK e (z r))
    (prefix_hrep W₁ W₂ hs₁ hs₂ η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ hY₁ hY₂ rows labels z vd hvd sc K hsc B hB)
    (fun e _ τ => hsource e τ)


#print axioms prefix_hrep
#print axioms prefix_weighted_separation
end
end QRH.Cycle092.GroupedPair
