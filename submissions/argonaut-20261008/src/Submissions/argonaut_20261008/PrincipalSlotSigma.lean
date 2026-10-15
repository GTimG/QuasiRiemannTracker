import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSlotEstimate
import Submissions.argonaut_20261008.EulerSigma

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Complex
namespace SevenEighths.PrincipalSlotEstimate
open ProbeEuler ProbeLocal

/- Static source revision over the actual imported definitions. Replay status: NOT_RUN. -/
theorem principal_correction_defect_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have h := unramifiedClosed_sigma_region_bound Q b A η 1 s 1 (1 / 6)
    (by linarith) hA hη (by simp) hblo hbhi hs (by norm_num) (by norm_num)
  calc
    _ ≤ 240 * Q ^ (-b-(47/50:ℝ)) := h
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem principal_correction_lower_bound_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have h := principal_correction_defect_sigma hblo hbhi hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem principal_correction_ne_zero_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (principal_correction_lower_bound_sigma hblo hbhi hQ hA hη hs)

theorem principal_correction_inverse_bound_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hl := principal_correction_lower_bound_sigma hblo hbhi hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr
  linarith

theorem principal_marked_error_bounds_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : b ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-b) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-b) := by
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
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-b) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-b) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤
      Q ^ (-b) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤ Q ^ (-b) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem principal_replacement_error_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : b ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-b) := by
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
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-b) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-b) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := principal_marked_error_bounds_sigma hblo hbhi hQ hA hη hs
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem principal_slot_error_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : b ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-b) := by
  have hn := principal_correction_ne_zero_sigma hblo hbhi hQ hA hη.le hs
  have he := principal_replacement_error_sigma hblo hbhi hQ hA hη hs
  have hi := principal_correction_inverse_bound_sigma hblo hbhi hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-b)) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_principal_slot_error_sigma {b : ℝ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1) (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : b ≤ s.re) :
    ‖principalSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-b) :=
  principal_slot_error_sigma hblo hbhi hQ (actualAPhase_norm_le_one η p) (actual_target_norm η p hp) hs

theorem weighted_principal_slot_error_sigma {b : ℝ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1) {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : b ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-b)) * ∑ i ∈ S, w i := by
  apply weighted_slot_error S w _ _ hw
  intro i hi
  apply (principal_slot_error_sigma hblo hbhi (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by linarith)

theorem weighted_principal_product_error_sigma {b : ℝ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1) {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : b ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-b)) ^ S.card - 1 := by
  apply fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact weighted_principal_slot_error_sigma hblo hbhi (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

theorem principal_geometric_bounds_sigma {b Q : ℝ} {η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
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

theorem principal_correction_eq_raw_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) =
      localCorrection (coordV Q (1 / 6)) (coordW Q 1 1) (coordD Q η 1 s)
        (principalMarked Q A η s) := by
  have h := principal_geometric_bounds_sigma hblo hbhi hQ hη hs
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem principal_raw_lower_bound_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    1 / 16 ≤ ‖principalRawFactor Q A η s‖ := by
  have hl := principal_correction_lower_bound_sigma hblo hbhi hQ hA hη hs
  have hg := principal_geometric_bounds_sigma hblo hbhi hQ hη hs
  have hV : ‖1 - coordV Q (1 / 6)‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q (1 / 6))
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 1‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 1)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      8 * ‖principalRawFactor Q A η s‖ := by
    rw [principal_correction_eq_raw_sigma hblo hbhi hQ hη hs]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖principalRawFactor Q A η s‖ *
      (‖1 - coordV Q (1 / 6)‖ * ‖1 - coordW Q 1 1‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖principalRawFactor Q A η s‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem principal_raw_ne_zero_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    principalRawFactor Q A η s ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (principal_raw_lower_bound_sigma hblo hbhi hQ hA hη hs)

theorem principal_slot_eq_raw_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : b ≤ s.re) :
    principalSlot Q A η s =
      (star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) := by
  have hg := principal_geometric_bounds_sigma hblo hbhi hQ hη hs
  have hn := principal_correction_ne_zero_sigma hblo hbhi hQ hA hη hs
  have hp := principal_raw_ne_zero_sigma hblo hbhi hQ hA hη hs
  have hr := compensatedReplacement_eq_raw (coordV Q (1 / 6)) (coordW Q 1 1)
    (coordD Q η 1 s) (principalMarked Q A η s) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-1 : ℂ))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← principal_correction_eq_raw_sigma hblo hbhi hQ hη hs] at hr
  unfold principalSlot principalReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem principal_raw_slot_error_sigma {b Q : ℝ} {A η s : ℂ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1)
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : b ≤ s.re) :
    ‖(star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) + 1‖ ≤ 1440 * Q ^ (-b) := by
  rw [← principal_slot_eq_raw_sigma hblo hbhi hQ hA hη.le hs]
  exact principal_slot_error_sigma hblo hbhi hQ hA hη hs

theorem weighted_principal_product_error_linear_sigma {b : ℝ}
    (hblo : (79/100:ℝ) ≤ b) (hbhi : b ≤ 1) {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : b ≤ s.re)
    (hsmall : 1440 * P ^ (-b) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-b)) :=
  (weighted_principal_product_error_sigma hblo hbhi S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (product_error_linear S.card (by positivity) hsmall)

theorem principal_slot_error_b0 {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1)
    (hs : (3499999/4000000:ℝ) ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-(3499999/4000000:ℝ)) :=
  principal_slot_error_sigma (by norm_num) (by norm_num) hQ hA hη hs

end SevenEighths.PrincipalSlotEstimate
end
end OAI

