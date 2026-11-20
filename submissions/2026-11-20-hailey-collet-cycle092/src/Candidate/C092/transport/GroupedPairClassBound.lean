/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Two-character row adaptation of Sil's common-profile separation.
The original one-column Fourier/profile lemmas and majorants are reused unchanged. -/
import Candidate.C092.transport.GroupedPairClassRows

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

open ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice (ballProfile ballProfile_nonneg ballProfile_le_one ballProfile_one)
open QRH.SilDensitySplit.CubeFree.Packet.Grouped (dilate_log_mem rescale_factor_le
  ball_lt_of_ne_zero mem_rowNormBall_of_norm_sq_le ball_one_of_le)

theorem class_bound {Λ : Type*} (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ : ℝ) (keep : O → Prop)
    (hkeep : ∀ y, keep y → y ≠ 0)
    (p₀ p₁ : 𝓢(ℝ, ℂ)) (hs₀ : Function.support (p₀ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₁ : Function.support (p₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (Y₁ Y₂ Kc : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hKc : 0 < Kc)
    (labels : Finset Λ) (weight : Λ → ℝ) (hweight : ∀ x, 0 ≤ weight x) (V : Λ → O) (K : Λ → ℝ)
    (hK : ∀ x ∈ labels, 0 < ((Ideal.span {V x}).absNorm : ℝ) * K x)
    (hscale : ∀ x ∈ labels, 2 * (((Ideal.span {V x}).absNorm : ℝ) * K x) ≤ Kc)
    (X₁ X₂ : Λ → ℝ)
    (hX : ∀ x ∈ labels, 0 < X₁ x ∧ Y₁ / 2 ≤ X₁ x ∧ X₁ x ≤ Y₁ ∧
      0 < X₂ x ∧ Y₂ / 2 ≤ X₂ x ∧ X₂ x ≤ Y₂)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ y : O, y ≠ 0 → ‖eisEmbedding y‖ ^ 2 ≤ Kc →
      ∑ x ∈ labels.filter (fun x => V x ∣ y), weight x ≤ D)
    (C T : ℝ) (J : ℕ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hsource : ∀ (e : Fin 2×Fin 2) (τ : ℝ×ℝ) (s : Finset O),
      (∀ y∈s,keep y ∧ ‖eisEmbedding y‖^2 ≤ Kc) →
      (∑ y∈s,‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ y‖^2) ≤ C*pairWeight J τ*T) :
    ∑ x ∈ labels, weight x * pairEnergy η₁ η₂ m A₁ A₂ mark t₁ t₂ p₀ p₁ (X₁ x) (X₂ x)
        (fun y => V x ∣ y ∧ keep y) ballProfile (((Ideal.span {V x}).absNorm : ℝ) * K x) ≤
      (4 * D) * C * (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ, 1 * pairMajorant p₀ p₁ hs₀ hs₁ e τ) *
        (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
          1 * pairMajorant p₀ p₁ hs₀ hs₁ e τ * pairWeight J τ) * T := by
  classical
  set Ball : Finset O := ShortDraftLatticeCount.rowNormBall ⌈2 * Kc⌉₊ with hBall
  set rows : Finset O := Ball.filter (fun y => keep y ∧ ‖eisEmbedding y‖ ^ 2 ≤ Kc) with hrows
  let ρ : Λ → ℝ := fun x => Real.sqrt (Y₁ * Y₂ / (X₁ x * X₂ x))
  let vd : Λ → ℝ × ℝ := fun x => (Real.log (Y₁ / X₁ x), Real.log (Y₂ / X₂ x))
  let B : Λ → O → ℂ := fun x y =>
    row η₁ η₂ m A₁ A₂ y (dilate p₀ (vd x).1) (dilate p₁ (vd x).2) t₁ t₂ Y₁ Y₂ mark
  let bw : Λ → O → ℝ := fun x y => if V x ∣ y then
    (ballProfile (‖eisEmbedding y‖ ^ 2 / (((Ideal.span {V x}).absNorm : ℝ) * K x))).re else 0
  let w : Λ → O → ℝ := fun x y => weight x * ρ x ^ 2 * bw x y
  have hbw0 : ∀ x y, 0 ≤ bw x y := by
    intro x y
    by_cases hv : V x ∣ y
    · simp only [bw, hv, if_true]; exact ballProfile_nonneg _
    · simp only [bw, hv, if_false, le_refl]
  have hw0 : ∀ x y, 0 ≤ w x y := fun x y =>
    mul_nonneg (mul_nonneg (hweight x) (sq_nonneg _)) (hbw0 x y)
  -- Step 1: each child energy is a finite row sum of rescaled rows.
  have hstep1 : ∀ x ∈ labels,
      pairEnergy η₁ η₂ m A₁ A₂ mark t₁ t₂ p₀ p₁ (X₁ x) (X₂ x) (fun y => V x ∣ y ∧ keep y) ballProfile
          (((Ideal.span {V x}).absNorm : ℝ) * K x) =
        ∑ y ∈ rows, ρ x ^ 2 * bw x y * ‖B x y‖ ^ 2 := by
    intro x hx
    obtain ⟨hX₁, hX₁l, hX₁u, hX₂, hX₂l, hX₂u⟩ := hX x hx
    unfold pairEnergy
    rw [tsum_eq_sum (s := rows)]
    · apply Finset.sum_congr rfl
      intro y hy
      have hk : keep y := (Finset.mem_filter.mp hy).2.1
      by_cases hv : V x ∣ y
      · have hc : V x ∣ y ∧ keep y := ⟨hv, hk⟩
        rw [if_pos hc]
        simp only [bw, hv, if_true]
        rw [row_rescale η₁ η₂ m A₁ A₂ y mark p₀ p₁ t₁ t₂ (X₁ x) (X₂ x) Y₁ Y₂ hX₁ hX₂ hY₁ hY₂,
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        ring
      · have hc : ¬ (V x ∣ y ∧ keep y) := fun h => hv h.1
        rw [if_neg hc]
        simp only [bw, hv, if_false, mul_zero, zero_mul]
    · intro y hy
      by_cases hc : V x ∣ y ∧ keep y
      · rw [if_pos hc]
        have hb : (ballProfile (‖eisEmbedding y‖ ^ 2 /
            (((Ideal.span {V x}).absNorm : ℝ) * K x))).re = 0 := by
          by_contra hne
          have hlt := ball_lt_of_ne_zero _ _ (sq_nonneg _) (hK x hx) hne
          have hle : ‖eisEmbedding y‖ ^ 2 ≤ Kc := by linarith [hscale x hx]
          apply hy
          refine Finset.mem_filter.mpr ⟨mem_rowNormBall_of_norm_sq_le _ _ ?_, hc.2, hle⟩
          linarith
        rw [hb, mul_zero]
      · rw [if_neg hc]
  -- Step 2: swap the label and row sums.
  have hstep2 : ∑ x ∈ labels, weight x * pairEnergy η₁ η₂ m A₁ A₂ mark t₁ t₂ p₀ p₁ (X₁ x) (X₂ x)
        (fun y => V x ∣ y ∧ keep y) ballProfile (((Ideal.span {V x}).absNorm : ℝ) * K x) =
      ∑ y ∈ rows, ∑ x ∈ labels, w x y * ‖B x y‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [hstep1 x hx])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro x _
    simp only [w]; ring
  rw [hstep2]
  -- Step 3: weighted common-profile separation.
  have hvd : ∀ r ∈ rows, ∀ l ∈ (fun _ : O => labels) r,
      (vd l).1 ∈ Set.Icc 0 (Real.log 2) ∧ (vd l).2 ∈ Set.Icc 0 (Real.log 2) := by
    intro r _ l hl
    obtain ⟨hX₁, hX₁l, hX₁u, hX₂, hX₂l, hX₂u⟩ := hX l hl
    exact ⟨dilate_log_mem _ _ hX₁ hX₁l hX₁u, dilate_log_mem _ _ hX₂ hX₂l hX₂u⟩
  have hDrow : ∀ r ∈ rows, ∑ l ∈ (fun _ : O => labels) r, w l r ≤ 4 * D := by
    intro r hr
    have hk : keep r := (Finset.mem_filter.mp hr).2.1
    have hrK : ‖eisEmbedding r‖ ^ 2 ≤ Kc := (Finset.mem_filter.mp hr).2.2
    have hle : ∀ l ∈ labels, w l r ≤ 4 * (if V l ∣ r then weight l else 0) := by
      intro l hl
      obtain ⟨hX₁, hX₁l, _, hX₂, hX₂l, _⟩ := hX l hl
      have hρ := rescale_factor_le Y₁ Y₂ (X₁ l) (X₂ l) hX₁ hX₂ hX₁l hX₂l hY₁.le hY₂.le
      by_cases hv : V l ∣ r
      · simp only [w, bw, hv, if_true]
        have hb1 := ballProfile_le_one (‖eisEmbedding r‖ ^ 2 /
          (((Ideal.span {V l}).absNorm : ℝ) * K l))
        have hb0 := ballProfile_nonneg (‖eisEmbedding r‖ ^ 2 /
          (((Ideal.span {V l}).absNorm : ℝ) * K l))
        have hweightl := hweight l
        have h1 : ρ l ^ 2 * (ballProfile (‖eisEmbedding r‖ ^ 2 /
            (((Ideal.span {V l}).absNorm : ℝ) * K l))).re ≤ 4 :=
          by nlinarith [sq_nonneg (ρ l)]
        nlinarith
      · simp only [w, bw, hv, if_false, mul_zero, le_refl]
    calc ∑ l ∈ labels, w l r ≤ ∑ l ∈ labels, 4 * (if V l ∣ r then weight l else 0) :=
          Finset.sum_le_sum hle
      _ = 4 * ∑ x ∈ labels.filter (fun x => V x ∣ r), weight x := by
          rw [← Finset.mul_sum, Finset.sum_filter]
      _ ≤ 4 * D := by linarith [hD r (hkeep r hk) hrK]
  have hsrc : ∀ (e : Fin 2×Fin 2) (τ : ℝ×ℝ),
      (∑ r∈rows,‖commonRow η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ e τ (id r)‖^2) ≤ C*pairWeight J τ*T:=by
    intro e τ
    exact hsource e τ rows (fun r hr=>(Finset.mem_filter.mp hr).2)
  exact prefix_weighted_separation p₀ p₁ hs₀ hs₁ η₁ η₂ m A₁ A₂ mark t₁ t₂ Y₁ Y₂ hY₁ hY₂
    rows (fun _ => labels) id vd hvd (fun _ _ => 1) 1 zero_le_one
    (fun _ _ _ _ => by simp) B (fun r _ l _ => by simp only [B, one_mul, id]) w (4 * D) C T J
    hw0 (by linarith) hDrow hC hT hsrc

#print axioms class_bound
end
end QRH.Cycle092.GroupedPair
