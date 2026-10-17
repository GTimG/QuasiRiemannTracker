import Candidate.Cycle63.Marked.DeletionMaxAmplitude

/-! Exact asymmetric marked gain. This module proves finite scalar and
max-product transport only; it supplies no analytic moment or endpoint. -/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OAI.SevenEighths.ExactMarkedGain
noncomputable section
open scoped Classical BigOperators

def gain (phi u v S : ℝ) : ℝ :=
  phi * (2 * min S u + min S v) / 3

def scaledGain (phi u v S D : ℝ) : ℝ :=
  gain phi (u * D) (v * D) S

theorem min_increment_le (S T cap : ℝ) (hST : S ≤ T) :
    min T cap - min S cap ≤ T - S := by
  rcases le_total cap S with hcap | hcap
  · rw [min_eq_right hcap, min_eq_right (hcap.trans hST)]
    linarith
  · rw [min_eq_left hcap]
    exact sub_le_sub_right (min_le_left _ _) S

theorem gain_mono (phi u v : ℝ) (hphi : 0 ≤ phi) :
    Monotone (gain phi u v) := by
  intro S T hST
  have hu := min_le_min_right u hST
  have hv := min_le_min_right v hST
  have hh : 2 * min S u + min S v ≤ 2 * min T u + min T v := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hh hphi
  dsimp [gain]
  linarith

theorem gain_increment_le (phi u v S T : ℝ) (hphi : 0 ≤ phi)
    (hST : S ≤ T) :
    gain phi u v T - gain phi u v S ≤ phi * (T - S) := by
  have hu := min_increment_le S T u hST
  have hv := min_increment_le S T v hST
  have hh : (2 * min T u + min T v) - (2 * min S u + min S v) ≤
      3 * (T - S) := by linarith
  have hm := mul_le_mul_of_nonneg_left hh hphi
  dsimp [gain]
  nlinarith

theorem gain_nonneg (phi u v S : ℝ) (hphi : 0 ≤ phi)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hS : 0 ≤ S) :
    0 ≤ gain phi u v S := by
  dsimp [gain]
  exact div_nonneg (mul_nonneg hphi (by positivity)) (by norm_num)

theorem gain_zero (phi u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    gain phi u v 0 = 0 := by
  simp only [gain, min_eq_left hu, min_eq_left hv, mul_zero, add_zero, zero_div]

theorem gain_le_linear (phi u v S : ℝ) (hphi : 0 ≤ phi) :
    gain phi u v S ≤ phi * S := by
  have hu := min_le_left S u
  have hv := min_le_left S v
  have hh : 2 * min S u + min S v ≤ 3 * S := by linarith
  have hm := mul_le_mul_of_nonneg_left hh hphi
  dsimp [gain]
  nlinarith

/-- The exact analogue of Deletion26.marked_exponent_monotone. -/
theorem source_amplitude_mono (delta phi u v S T : ℝ)
    (hphi : 0 ≤ phi) (hphi_delta : phi ≤ delta) (hST : S ≤ T) :
    delta * S - gain phi u v S ≤ delta * T - gain phi u v T := by
  have hg := gain_increment_le phi u v S T hphi hST
  have hd := mul_nonneg (sub_nonneg.mpr hphi_delta) (sub_nonneg.mpr hST)
  nlinarith

theorem source_amplitude_monotone (delta phi u v : ℝ)
    (hphi : 0 ≤ phi) (hphi_delta : phi ≤ delta) :
    Monotone (fun S : ℝ => delta * S - gain phi u v S) := by
  intro S T hST
  exact source_amplitude_mono delta phi u v S T hphi hphi_delta hST

theorem scaledGain_mono_width (phi u v D : ℝ) (hphi : 0 ≤ phi) :
    Monotone (fun S : ℝ => scaledGain phi u v S D) :=
  gain_mono phi (u * D) (v * D) hphi

theorem scaledGain_mono_scale (phi u v S : ℝ) (hphi : 0 ≤ phi)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Monotone (fun D : ℝ => scaledGain phi u v S D) := by
  intro D E hDE
  have huD := mul_le_mul_of_nonneg_left hDE hu
  have hvD := mul_le_mul_of_nonneg_left hDE hv
  have hmu := min_le_min_left S huD
  have hmv := min_le_min_left S hvD
  have hh : 2 * min S (u * D) + min S (v * D) ≤
      2 * min S (u * E) + min S (v * E) := by linarith
  have hm := mul_le_mul_of_nonneg_left hh hphi
  dsimp [scaledGain, gain]
  linarith

theorem scaledGain_homogeneous (phi u v S D : ℝ) (hD : 0 ≤ D) :
    scaledGain phi u v (D * S) D = D * gain phi u v S := by
  have hu : min (D * S) (u * D) = D * min S u := by
    rw [mul_comm u D, mul_min_of_nonneg _ _ hD]
  have hv : min (D * S) (v * D) = D * min S v := by
    rw [mul_comm v D, mul_min_of_nonneg _ _ hD]
  dsimp [scaledGain, gain]
  rw [hu, hv]
  ring

theorem scaledGain_le_linear (phi u v S D : ℝ) (hphi : 0 ≤ phi) :
    scaledGain phi u v S D ≤ phi * S :=
  gain_le_linear phi (u * D) (v * D) S hphi

theorem scaledGain_le_capacity (phi u v S D : ℝ) (hphi : 0 ≤ phi) :
    scaledGain phi u v S D ≤ (phi * (2 * u + v) / 3) * D := by
  have hu := min_le_right S (u * D)
  have hv := min_le_right S (v * D)
  have hh : 2 * min S (u * D) + min S (v * D) ≤
      2 * (u * D) + v * D := by linarith
  have hm := mul_le_mul_of_nonneg_left hh hphi
  dsimp [scaledGain, gain]
  nlinarith

theorem scaledGain_le_row_mass (phi u v S D rho : ℝ)
    (hphi : 0 ≤ phi) (hD : 0 ≤ D)
    (hcapacity : phi * (2 * u + v) / 3 ≤ rho) :
    scaledGain phi u v S D ≤ rho * D := by
  exact (scaledGain_le_capacity phi u v S D hphi).trans
    (mul_le_mul_of_nonneg_right hcapacity hD)

/-- Exact-G counterpart of the existing finite powerset transport.
All moment estimates remain explicit hypotheses. -/
theorem max_weighted_row_sum {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C rho delta phi u v loss : ℝ)
    (hw : ∀ s ∈ slots, 0 ≤ w s) (hU : 1 ≤ U) (hC : 0 ≤ C)
    (hphi : 0 ≤ phi) (hphi_delta : phi ≤ delta)
    (hsub : ∀ J ⊆ slots, (∑ x ∈ rows, ‖∏ s ∈ J, Q x s‖ ^ 2) ≤
      C * U ^ (rho + delta * (∑ s ∈ J, w s) -
        gain phi u v (∑ s ∈ J, w s) + loss)) :
    (∑ x ∈ rows, (∏ s ∈ slots, max 1 ‖Q x s‖) ^ 2) ≤
      (2 : ℝ) ^ slots.card * C * U ^
        (rho + delta * (∑ s ∈ slots, w s) -
          gain phi u v (∑ s ∈ slots, w s) + loss) := by
  have hs (J : Finset Slot) (hJ : J ⊆ slots) :
      rho + delta * (∑ s ∈ J, w s) - gain phi u v (∑ s ∈ J, w s) + loss ≤
        rho + delta * (∑ s ∈ slots, w s) -
          gain phi u v (∑ s ∈ slots, w s) + loss := by
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hJ (fun s hs _ => hw s hs)
    linarith [source_amplitude_mono delta phi u v _ _ hphi hphi_delta hsum]
  calc
    _ ≤ ∑ x ∈ rows, ∑ J ∈ slots.powerset, ‖∏ s ∈ J, Q x s‖ ^ 2 :=
      Finset.sum_le_sum (fun x _ => Deletion26.max_product_le_powerset slots (Q x))
    _ = ∑ J ∈ slots.powerset, ∑ x ∈ rows, ‖∏ s ∈ J, Q x s‖ ^ 2 :=
      Finset.sum_comm
    _ ≤ ∑ J ∈ slots.powerset,
        C * U ^ (rho + delta * (∑ s ∈ slots, w s) -
          gain phi u v (∑ s ∈ slots, w s) + loss) := by
      apply Finset.sum_le_sum
      intro J hJ
      have hJs := Finset.mem_powerset.mp hJ
      exact (hsub J hJs).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU (hs J hJs)) hC)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- Empty subsets use the ordinary count; nonempty subsets keep exact G. -/
theorem max_weighted_row_sum_of_nonempty {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C rho delta phi u v loss : ℝ)
    (hw : ∀ s ∈ slots, 0 ≤ w s) (hU : 1 ≤ U) (hC : 0 ≤ C)
    (hphi : 0 ≤ phi) (hphi_delta : phi ≤ delta) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcount : (rows.card : ℝ) ≤ C * U ^ (rho + loss))
    (hsub : ∀ J ⊆ slots, J.Nonempty →
      (∑ x ∈ rows, ‖∏ s ∈ J, Q x s‖ ^ 2) ≤
        C * U ^ (rho + delta * (∑ s ∈ J, w s) -
          gain phi u v (∑ s ∈ J, w s) + loss)) :
    (∑ x ∈ rows, (∏ s ∈ slots, max 1 ‖Q x s‖) ^ 2) ≤
      (2 : ℝ) ^ slots.card * C * U ^
        (rho + delta * (∑ s ∈ slots, w s) -
          gain phi u v (∑ s ∈ slots, w s) + loss) := by
  apply max_weighted_row_sum rows slots Q w U C rho delta phi u v loss
    hw hU hC hphi hphi_delta
  intro J hJ
  rcases J.eq_empty_or_nonempty with rfl | hne
  · simpa only [Finset.prod_empty, norm_one, one_pow, Finset.sum_const,
      Finset.sum_empty, nsmul_eq_mul, mul_one, mul_zero, gain_zero phi u v hu hv,
      sub_zero, add_zero] using hcount
  · exact hsub J hJ hne

end
end OAI.SevenEighths.ExactMarkedGain

#print axioms OAI.SevenEighths.ExactMarkedGain.gain_mono
#print axioms OAI.SevenEighths.ExactMarkedGain.gain_increment_le
#print axioms OAI.SevenEighths.ExactMarkedGain.source_amplitude_mono
#print axioms OAI.SevenEighths.ExactMarkedGain.scaledGain_mono_scale
#print axioms OAI.SevenEighths.ExactMarkedGain.scaledGain_homogeneous
#print axioms OAI.SevenEighths.ExactMarkedGain.scaledGain_le_row_mass
#print axioms OAI.SevenEighths.ExactMarkedGain.max_weighted_row_sum
#print axioms OAI.SevenEighths.ExactMarkedGain.max_weighted_row_sum_of_nonempty
