/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Two-character row adaptation of Sil's common-profile separation.
The original one-column Fourier/profile lemmas and majorants are reused unchanged. -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedRows
import Candidate.C092.transport.StrongPairFinite

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

/-- Two genuine independent ordinary factors times ONE frozen common mark.
The mark may be any fixed original normalized whole-slot subproduct. -/
def row (η₁ η₂ : Character) (m A₁ A₂ z : O) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ Y₁ Y₂ : ℝ) (mark : O→ℂ) : ℂ :=
  (Real.sqrt (Y₁*Y₂):ℂ)⁻¹*
    (rowTwistedSum η₁ m A₁ z W₁ t₁ Y₁*rowTwistedSum η₂ m A₂ z W₂ t₂ Y₂)*mark z

def commonRow (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ)
    (t₁ t₂ Y₁ Y₂ : ℝ) (e : Fin 2×Fin 2) (τ : ℝ×ℝ) (z : O) : ℂ :=
  row η₁ η₂ m A₁ A₂ z ((commonPair e τ).profile 0) ((commonPair e τ).profile 1)
    t₁ t₂ (scale e.1*Y₁) (scale e.2*Y₂) mark

theorem row_eq_original (η₁ η₂ : Character) (m A₁ A₂ z : O) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ Y₁ Y₂ : ℝ) (mark : O→ℂ) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) :
    row η₁ η₂ m A₁ A₂ z W₁ W₂ t₁ t₂ Y₁ Y₂ mark=
      original η₁ m A₁ z W₁ t₁ Y₁*original η₂ m A₂ z W₂ t₂ Y₂*mark z := by
  simp only [row,original,Real.sqrt_mul hY₁.le,Complex.ofReal_mul,mul_inv]
  ring

theorem commonRow_mul (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (η₁ η₂ : Character) (m A₁ A₂ z : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (e : Fin 2 × Fin 2) (v τ : ℝ × ℝ) :
    pairCoeff W₁ W₂ hs₁ hs₂ e v τ * commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ z =
      (Real.sqrt (Y₁ * Y₂) : ℂ)⁻¹ *
        ((cellCoeff W₁ hs₁ e.1 v.1 τ.1 *
            rowTwistedSum η₁ m A₁ z (commonProfile e.1 τ.1) t₁ (scale e.1 * Y₁)) *
          (cellCoeff W₂ hs₂ e.2 v.2 τ.2 *
            rowTwistedSum η₂ m A₂ z (commonProfile e.2 τ.2) t₂ (scale e.2 * Y₂))) *
        mark z := by
  have hc1 := scale_pos e.1
  have hc2 := scale_pos e.2
  have hsq : Real.sqrt (scale e.1 * Y₁ * (scale e.2 * Y₂)) =
      Real.sqrt (scale e.1 * scale e.2) * Real.sqrt (Y₁ * Y₂) := by
    rw [← Real.sqrt_mul (mul_pos hc1 hc2).le]
    congr 1
    ring
  have hne : (Real.sqrt (scale e.1 * scale e.2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hc1 hc2)).ne'
  have key : (Real.sqrt (scale e.1 * scale e.2) : ℂ) * (Real.sqrt (scale e.1 * scale e.2) : ℂ)⁻¹
      = 1 := mul_inv_cancel₀ hne
  simp only [commonRow, row, pairCoeff, commonPair_profile_zero,
    commonPair_profile_one]
  rw [hsq, Complex.ofReal_mul, mul_inv]
  linear_combination
    ((Real.sqrt (Y₁ * Y₂) : ℂ)⁻¹ * cellCoeff W₁ hs₁ e.1 v.1 τ.1 *
      cellCoeff W₂ hs₂ e.2 v.2 τ.2 *
      rowTwistedSum η₁ m A₁ z (commonProfile e.1 τ.1) t₁ (scale e.1 * Y₁) *
      rowTwistedSum η₂ m A₂ z (commonProfile e.2 τ.2) t₂ (scale e.2 * Y₂) *
      mark z) * key

/-- **Exact separation of the literal prefix-dilated positive slot row.** For prefix dilations
`v ∈ [0, log 2]²` of both ordinary profiles, normalized at the common scales `Y₁, Y₂`, the row is
a sum over the four tensored cells of spectral integrals of the common rows, with coefficient
`pairCoeff` (density, unimodular prefix and scale phases, and the retained `√(c_{e₁}c_{e₂})`). -/
theorem pair_row_separation (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (v : ℝ × ℝ) (hv₁ : v.1 ∈ Set.Icc 0 (Real.log 2)) (hv₂ : v.2 ∈ Set.Icc 0 (Real.log 2))
    (η₁ η₂ : Character) (m A₁ A₂ z : O) (mark : O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    row η₁ η₂ m A₁ A₂ z (dilate W₁ v.1) (dilate W₂ v.2) t₁ t₂ Y₁ Y₂ mark =
      ∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
        pairCoeff W₁ W₂ hs₁ hs₂ e v τ * commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ z := by
  set N : ℂ := (Real.sqrt (Y₁ * Y₂) : ℂ)⁻¹ with hN
  set Q₀ : ℂ := mark z with hQ₀
  set F₁ : Fin 2 → ℝ → ℂ := fun e₁ τ₁ => cellCoeff W₁ hs₁ e₁ v.1 τ₁ *
    rowTwistedSum η₁ m A₁ z (commonProfile e₁ τ₁) t₁ (scale e₁ * Y₁) with hF₁
  set F₂ : Fin 2 → ℝ → ℂ := fun e₂ τ₂ => cellCoeff W₂ hs₂ e₂ v.2 τ₂ *
    rowTwistedSum η₂ m A₂ z (commonProfile e₂ τ₂) t₂ (scale e₂ * Y₂) with hF₂
  have hcell : ∀ (e : Fin 2 × Fin 2),
      ∫ τ : ℝ × ℝ, pairCoeff W₁ W₂ hs₁ hs₂ e v τ * commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ z =
        N * ((∫ τ₁ : ℝ, F₁ e.1 τ₁) * (∫ τ₂ : ℝ, F₂ e.2 τ₂)) * Q₀ := by
    intro e
    have hpt : ∀ τ : ℝ × ℝ,
        pairCoeff W₁ W₂ hs₁ hs₂ e v τ * commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ z =
          N * (F₁ e.1 τ.1 * F₂ e.2 τ.2) * Q₀ := fun τ =>
      commonRow_mul W₁ W₂ hs₁ hs₂ η₁ η₂ m A₁ A₂ z mark t₁ t₂ Y₁ Y₂ e v τ
    simp_rw [hpt]
    rw [integral_mul_const, integral_const_mul]
    have hp := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (F₁ e.1) (F₂ e.2)
    rw [← Measure.volume_eq_prod] at hp
    rw [hp]
  simp only [row]
  rw [ProfileSeparation.rowTwisted_separation W₁ hs₁ v.1 hv₁.1 hv₁.2 η₁ m A₁ z t₁ Y₁ hY₁,
    ProfileSeparation.rowTwisted_separation W₂ hs₂ v.2 hv₂.1 hv₂.2 η₂ m A₂ z t₂ Y₂ hY₂]
  rw [Finset.sum_congr rfl (fun e _ => hcell e), Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e₁ _
  apply Finset.sum_congr rfl
  intro e₂ _
  simp only [hN, hQ₀, hF₁, hF₂]


#print axioms pair_row_separation
#print axioms row_eq_original
end
end QRH.Cycle092.GroupedPair
