import WeightedQRH.CertificateBernstein

namespace WeightedQRH
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The original high exponent with an arbitrary proved row count. -/
def genericOldExponent (d δ q R : ℝ) : ℝ :=
  (1 + δ) / 2 - theta + h * (17 / 50 - 1 / 6) -
  (1 + δ) / 2 * ly - ell / 2 + q * ell + d * (R + δ / 2 - 17 / 50)

/-- Original pointwise-numerator bound, with the actual selected row count. -/
def oldExponent (d δ x : ℝ) : ℝ :=
  genericOldExponent d δ (δ * x) (rowCount δ x)

/-- New physical-numerator moment bound, including its prime capacity saving. -/
def weightedExponent (d δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - theta + h * (17 / 50 - 1 / 6) - ly / 2 - ell / 2 + δ * x * ell +
  d * ((3 * rowCount δ x + 1) / 4 - 17 / 50) - δ * x * (2 * ly - d) / (12 * kappa)

theorem rowCount_formula {δ x : ℝ} (hJ : countDen δ x ≠ 0) :
    rowCount δ x = 1 - δ + (5 / 6 - δ) * δ * countP x / (2 * countDen δ x) := by
  unfold rowCount countNum
  field_simp [hJ]
  <;> ring

theorem rowCount_lower {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 - δ ≤ rowCount δ x := by
  have hJ := countDen_pos hδ0 hδ1 hx0 hx1
  have ha : 0 ≤ (5 / 6 : ℝ) - δ := by linarith
  have hp : 0 ≤ countP x := by
    have hp1 : 0 ≤ (2 : ℝ) - 8 / 9 * x := by linarith
    have hp2 : 0 ≤ (1 : ℝ) - x := by linarith
    exact mul_nonneg hp1 hp2
  have hn : 0 ≤ (5 / 6 - δ) * δ * countP x :=
    mul_nonneg (mul_nonneg ha hδ0) hp
  rw [rowCount_formula hJ.ne']
  have hdiv : 0 ≤ (5 / 6 - δ) * δ * countP x / (2 * countDen δ x) := by positivity
  linarith

theorem rowCount_upper {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    rowCount δ x ≤ 1 := by
  have hJ := countDen_pos hδ0 hδ1 hx0 hx1
  have ha : 0 ≤ (5 / 6 : ℝ) - δ := by linarith
  have hp : 0 ≤ countP x := by
    have hp1 : 0 ≤ (2 : ℝ) - 8 / 9 * x := by linarith
    have hp2 : 0 ≤ (1 : ℝ) - x := by linarith
    exact mul_nonneg hp1 hp2
  have hdp : 0 ≤ countD x - countP x / 2 := by
    have hxprod := mul_nonneg hx0 (sub_nonneg.mpr hx1)
    unfold countD countP
    nlinarith
  have hprod := mul_nonneg hδ0 (add_nonneg (mul_nonneg ha hdp) (mul_nonneg hδ0 hp))
  have hc : countNum δ x ≤ countDen δ x := by
    unfold countNum countDen
    nlinarith [hprod]
  unfold rowCount
  apply (div_le_iff₀ hJ).mpr
  simpa using hc

theorem oldCert_identity {δ x : ℝ} (hJ : countDen δ x ≠ 0) :
    oldCert δ x = -countDen δ x * (oldExponent h δ x + endpointMargin) := by
  unfold oldCert oldRest oldExponent genericOldExponent rowCount
  field_simp [hJ]
  <;> ring

theorem weightedCert_identity {δ x : ℝ} (hJ : countDen δ x ≠ 0) :
    weightedCert δ x = -countDen δ x * (weightedExponent h δ x + endpointMargin) := by
  unfold weightedCert oldCert oldRest weightedExponent rowCount kappa
  field_simp [hJ]
  <;> ring

/-- The full old-branch real rectangle, including the exact 1/10000 margin. -/
theorem old_endpoint_bound {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 3) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    oldExponent h δ x ≤ -(1 / 10000 : ℝ) := by
  have hJ := countDen_pos hδ0 (by linarith) hx0 hx1
  have hc := oldCert_nonneg hδ0 hδ1 hx0 hx1
  have hi := oldCert_identity hJ.ne'
  change oldExponent h δ x ≤ -endpointMargin
  apply (mul_le_mul_iff_right₀ hJ).mp
  nlinarith [hi]

/-- The full new-branch real rectangle, including the exact 1/10000 margin. -/
theorem weighted_endpoint_bound {δ x : ℝ}
    (hδ0 : 1 / 3 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    weightedExponent h δ x ≤ -(1 / 10000 : ℝ) := by
  have hJ := countDen_pos (by linarith) hδ1 hx0 hx1
  have hc := weightedCert_nonneg hδ0 hδ1 hx0 hx1
  have hi := weightedCert_identity hJ.ne'
  change weightedExponent h δ x ≤ -endpointMargin
  apply (mul_le_mul_iff_right₀ hJ).mp
  nlinarith [hi]

theorem old_frequency_slope_pos {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 < rowCount δ x + δ / 2 - 17 / 50 := by
  have hr := rowCount_lower hδ0 hδ1 hx0 hx1
  linarith

theorem weighted_frequency_slope_pos {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 < (3 * rowCount δ x + 1) / 4 - 17 / 50 + δ * x / (12 * kappa) := by
  have hr := rowCount_lower hδ0 hδ1 hx0 hx1
  have hq : 0 ≤ δ * x / (12 * kappa) := by unfold kappa; positivity
  linarith

theorem old_frequency_slope_le_two {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    rowCount δ x + δ / 2 - 17 / 50 ≤ 2 := by
  have hr := rowCount_upper hδ0 hδ1 hx0 hx1
  linarith

theorem weighted_frequency_slope_le_two {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (3 * rowCount δ x + 1) / 4 - 17 / 50 + δ * x / (12 * kappa) ≤ 2 := by
  have hr := rowCount_upper hδ0 hδ1 hx0 hx1
  have hp := mul_nonneg hδ0 (sub_nonneg.mpr hx1)
  norm_num [kappa]
  nlinarith

theorem old_row_difference (d δ x : ℝ) :
    oldExponent d δ x - oldExponent h δ x =
      (d - h) * (rowCount δ x + δ / 2 - 17 / 50) := by
  unfold oldExponent genericOldExponent
  ring

theorem weighted_row_difference (d δ x : ℝ) :
    weightedExponent d δ x - weightedExponent h δ x =
      (d - h) * ((3 * rowCount δ x + 1) / 4 - 17 / 50 + δ * x / (12 * kappa)) := by
  unfold weightedExponent
  ring

theorem old_moderate_bound {d δ x : ℝ} (hd : d ≤ h)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 3) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    oldExponent d δ x ≤ -(1 / 10000 : ℝ) := by
  have he := old_endpoint_bound hδ0 hδ1 hx0 hx1
  have hs := old_frequency_slope_pos hδ0 (by linarith) hx0 hx1
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hd) hs.le
  have hi := old_row_difference d δ x
  linarith

theorem weighted_moderate_bound {d δ x : ℝ} (hd : d ≤ h)
    (hδ0 : 1 / 3 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    weightedExponent d δ x ≤ -(1 / 10000 : ℝ) := by
  have he := weighted_endpoint_bound hδ0 hδ1 hx0 hx1
  have hs := weighted_frequency_slope_pos (by linarith) hδ1 hx0 hx1
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hd) hs.le
  have hi := weighted_row_difference d δ x
  linarith

theorem old_extended_bound {d δ x : ℝ} (hd : d ≤ h + rowExtension)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 3) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    oldExponent d δ x ≤ -(1 / 20000 : ℝ) := by
  have he := old_endpoint_bound hδ0 hδ1 hx0 hx1
  have hs := old_frequency_slope_pos hδ0 (by linarith) hx0 hx1
  have hs' := old_frequency_slope_le_two hδ0 (by linarith) hx0 hx1
  have hp : (d - h) * (rowCount δ x + δ / 2 - 17 / 50) ≤ rowExtension * 2 := by
    calc
      _ ≤ rowExtension * (rowCount δ x + δ / 2 - 17 / 50) :=
        mul_le_mul_of_nonneg_right (by linarith) hs.le
      _ ≤ rowExtension * 2 := mul_le_mul_of_nonneg_left hs' rowExtension_pos.le
  have hi := old_row_difference d δ x
  have hm := rowExtension_cost
  norm_num [endpointMargin] at hm
  linarith

theorem weighted_extended_bound {d δ x : ℝ} (hd : d ≤ h + rowExtension)
    (hδ0 : 1 / 3 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    weightedExponent d δ x ≤ -(1 / 20000 : ℝ) := by
  have he := weighted_endpoint_bound hδ0 hδ1 hx0 hx1
  have hs := weighted_frequency_slope_pos (by linarith) hδ1 hx0 hx1
  have hs' := weighted_frequency_slope_le_two (by linarith) hδ1 hx0 hx1
  have hp : (d - h) * ((3 * rowCount δ x + 1) / 4 - 17 / 50 + δ * x / (12 * kappa)) ≤
      rowExtension * 2 := by
    calc
      _ ≤ rowExtension * ((3 * rowCount δ x + 1) / 4 - 17 / 50 + δ * x / (12 * kappa)) :=
        mul_le_mul_of_nonneg_right (by linarith) hs.le
      _ ≤ rowExtension * 2 := mul_le_mul_of_nonneg_left hs' rowExtension_pos.le
  have hi := weighted_row_difference d δ x
  have hm := rowExtension_cost
  norm_num [endpointMargin] at hm
  linarith

/-- The contour choice depends only on the zero bin δ, never on x. -/
theorem binwise_uniform_bound {d δ : ℝ} (hd : d ≤ h)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    (δ ≤ 1 / 3 ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → oldExponent d δ x ≤ -endpointMargin) ∨
    (1 / 3 ≤ δ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → weightedExponent d δ x ≤ -endpointMargin) := by
  by_cases hb : δ ≤ 1 / 3
  · exact Or.inl ⟨hb, fun x hx0 hx1 => old_moderate_bound hd hδ0 hb hx0 hx1⟩
  · have hb' : 1 / 3 ≤ δ := by linarith
    exact Or.inr ⟨hb', fun x hx0 hx1 => weighted_moderate_bound hd hb' hδ1 hx0 hx1⟩

theorem floor_endpoint :
    genericOldExponent h (1 / 50) (1 / 100) 1 = -(893 / 75000 : ℝ) := by
  norm_num [genericOldExponent, theta, h, ly, ell]

theorem floor_row_bound {d : ℝ} (hd : d ≤ h) :
    genericOldExponent d (1 / 50) (1 / 100) 1 ≤ -(893 / 75000 : ℝ) := by
  norm_num [genericOldExponent, theta, h, ly, ell] at *
  linarith

theorem intermediate_endpoint_bound {δ : ℝ}
    (hδ0 : 1 / 50 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    genericOldExponent (1 / 2) δ (δ / 2) (76 / 75 - 2 * δ / 3) ≤
      -(4459 / 400000 : ℝ) := by
  norm_num [genericOldExponent, theta, h, ly, ell]
  linarith

theorem intermediate_row_bound {d δ : ℝ} (hd : d ≤ 1 / 2)
    (hδ0 : 1 / 50 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    genericOldExponent d δ (δ / 2) (76 / 75 - 2 * δ / 3) ≤
      -(4459 / 400000 : ℝ) := by
  have he := intermediate_endpoint_bound hδ0 hδ1
  have hs : 0 ≤ (76 / 75 : ℝ) - 2 * δ / 3 + δ / 2 - 17 / 50 := by linarith
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hd) hs
  have hi : genericOldExponent d δ (δ / 2) (76 / 75 - 2 * δ / 3) -
      genericOldExponent (1 / 2) δ (δ / 2) (76 / 75 - 2 * δ / 3) =
      (d - 1 / 2) * (76 / 75 - 2 * δ / 3 + δ / 2 - 17 / 50) := by
    unfold genericOldExponent
    ring
  linarith

end
end WeightedQRH
