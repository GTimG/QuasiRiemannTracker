/- Adapted from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Cycle25.Assembly.Transport.GeometryFacts
import Cycle25.Assembly.Low.RegionalCorrection
import OAI.NumberTheory.DirichletL.PrincipalSlotEstimate

/-!
Principal slot bounds for the original compensated Euler factors at the new
boundary. Adapted from the original OpenAI PrincipalSlotEstimate proofs;
all slot definitions are imported unchanged.
-/
noncomputable section
open scoped Classical BigOperators
open Complex OAI OAI.SevenEighths
namespace Cycle25.Transport.PrincipalSlots
open Cycle25.LowCorrection
open ProbeEuler ProbeLocal PrincipalSlotEstimate

theorem principal_correction_defect {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hθ := Cycle25.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have h := weighted_unramified_bound Q A η 1 s 1 (1 / 6)
    (by linarith) hA hη (by simp) hs (by norm_num) (by norm_num)
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) := h
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem principal_correction_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have hθ := Cycle25.Transport.theta_bounds
  have h := principal_correction_defect hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem principal_correction_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
  have hθ := Cycle25.Transport.theta_bounds
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (principal_correction_lower_bound hQ hA hη hs)

theorem principal_correction_inverse_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hθ := Cycle25.Transport.theta_bounds
  have hl := principal_correction_lower_bound hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr
  linarith

theorem principal_marked_error_bounds {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-theta) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-theta) := by
  have hθ := Cycle25.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by
    have h := coordW_norm_le Q hQ0 (1 : ℂ) 1 (by simp)
    norm_num at h
    exact h.trans (by simpa using hpow (-1) 0 (by norm_num))
  have hR : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖coordD Q η 1 s‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hK : ‖coordK Q η s 1‖ ≤ Q ^ (-s.re) := by
    convert coordK_norm_le Q hQ1 η s 1 hη.le using 1
    norm_num
  have hB := principal_B_norm hQ0 η s hη
  have hRhalf : ‖coordR Q A s (1 / 6)‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q (3 - 6 * s.re) hQ4 (by linarith))
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hDhalf : ‖coordD Q η 1 s‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← principal_V]; linarith
  have hE := unramified_marked_error_bound (coordR Q A s (1 / 6))
    (coordV Q (1 / 6)) (Q : ℂ)⁻¹ (coordK Q η s 1) (coordW Q 1 1)
    (coordD Q η 1 s) hRhalf hVhalf hq hDhalf
  change ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-theta) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-theta) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤
      Q ^ (-theta) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤ Q ^ (-theta) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by first | (solve | norm_num) | (linarith [Cycle25.Transport.theta_bounds]))
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem principal_replacement_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-theta) := by
  have hθ := Cycle25.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hD := coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hDhalf := hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hWq : coordW Q 1 1 = (Q : ℂ) ^ (-1 : ℂ) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    rw [Complex.cpow_neg_one, ← principal_V]; linarith
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by rw [hWq]; exact hq
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-theta) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by first | (solve | norm_num) | (linarith [Cycle25.Transport.theta_bounds]))
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-theta) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := principal_marked_error_bounds hQ hA hη hs
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem principal_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-theta) := by
  have hθ := Cycle25.Transport.theta_bounds
  have hn := principal_correction_ne_zero hQ hA hη.le hs
  have he := principal_replacement_error hQ hA hη hs
  have hi := principal_correction_inverse_bound hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-theta)) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem weighted_principal_slot_error {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : theta ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-theta)) * ∑ i ∈ S, w i := by
  have hθ := Cycle25.Transport.theta_bounds
  apply weighted_slot_error S w _ _ hw
  intro i hi
  apply (principal_slot_error (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by first | (solve | norm_num) | (linarith [Cycle25.Transport.theta_bounds]))

theorem weighted_principal_product_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : theta ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-theta)) ^ S.card - 1 := by
  have hθ := Cycle25.Transport.theta_bounds
  apply fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact weighted_principal_slot_error (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

theorem principal_geometric_bounds {Q : ℝ} {η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hθ := Cycle25.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    norm_num
    exact rpow_le_half Q (-1) hQ4 (by norm_num)
  refine ⟨hV, ?_, ?_⟩
  · rw [principal_W, ← principal_V]; exact hV
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q (-s.re) hQ4 (by linarith))

theorem weighted_principal_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : theta ≤ s.re)
    (hsmall : 1440 * P ^ (-theta) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-theta)) :=
  (weighted_principal_product_error S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (product_error_linear S.card (by positivity) hsmall)

theorem region_correction_defect {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hθ := Cycle25.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) :=
      weighted_unramified_bound Q A η 1 s w z (by linarith) hA hη (by simp) hs hw hz
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem region_correction_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by
  have hθ := Cycle25.Transport.theta_bounds
  have h := region_correction_defect hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem region_correction_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z ≠ 0 := by
  have hθ := Cycle25.Transport.theta_bounds
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (region_correction_lower_bound hQ hA hη hs hw hz)

theorem region_correction_inverse_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hθ := Cycle25.Transport.theta_bounds
  have hl := region_correction_lower_bound hQ hA hη hs hw hz
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr
  linarith

theorem region_geometric_bounds {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hθ := Cycle25.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem region_marked_error_bounds {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-theta) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-theta) := by
  have hθ := Cycle25.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := principal_B_norm hQ0 η s hη
  have hg := region_geometric_bounds hQ hη.le hs hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-theta) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-theta) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-theta) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-theta) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ + 4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem region_replacement_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-theta) := by
  have hθ := Cycle25.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := region_geometric_bounds hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-theta) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-theta) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := region_marked_error_bounds hQ hA hη hs hw hz
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem region_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-theta) := by
  have hθ := Cycle25.Transport.theta_bounds
  have hn := region_correction_ne_zero hQ hA hη.le hs hw hz
  have he := region_replacement_error hQ hA hη hs hw hz
  have hi := region_correction_inverse_bound hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-theta)) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem region_slot_norm_le {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤ 1 + 1440 * Q ^ (-theta) := by
  have hθ := Cycle25.Transport.theta_bounds
  have he := region_slot_error hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem weighted_region_slot_norm {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : theta ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-theta)) * ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  have hθ := Cycle25.Transport.theta_bounds
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-theta)) * (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := region_slot_norm_le (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤ 1 + 1440 * P ^ (-theta) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by first | (solve | norm_num) | (linarith [Cycle25.Transport.theta_bounds]))
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

end Cycle25.Transport.PrincipalSlots
end
