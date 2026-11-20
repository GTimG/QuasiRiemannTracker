/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.ActualMixedPrice
set_option autoImplicit false
namespace QRH.Cycle092.ActualMixedPrice
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
open QRH.ContactCertificate QRH.Coverage
noncomputable section

/-- The same original Q1 debit remains valid through the actual supported
conductor extension, paying its entire possible increment explicitly. -/
theorem padded_debit {r : Row} (hr : r∈rows)
    {h x D : ℝ} {point : Point}
    (hh : hLower≤h) (hh' : h≤hUpper) (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : 0≤D) (hDh : D≤h+rowPad) :
    excess h point.1 point.2 x D ≤ D*(rowBudget r.B : ℝ)+rowPad := by
  have hs := Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have hcast : (rowBudget r.B : ℝ)=Top.debit r := rowBudget_cast hs.1
  have hpad : 0≤rowPad := allowances_pos.2.1.le
  by_cases hle : D≤h
  · have hb := Top.every_row_normalized_debit hr hh hh' hp hx hD hle
    rw [←hcast] at hb
    exact hb.trans (le_add_of_nonneg_right hpad)
  · have hhD : h≤D := le_of_not_ge hle
    have hg := Top.point_guards hs hp
    have hc := Physical.actual_contact_bounds hx
    have hi := Physical.price_increment_le hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hhD
    have hh₀ : 0≤h := (by norm_num [hLower] : (0 : ℝ)≤hLower).trans hh
    have hb := Top.every_row_normalized_debit hr hh hh' hp hx hh₀ le_rfl
    rw [←hcast] at hb
    have hq := budget_nonnegative hr
    have hm := mul_le_mul_of_nonneg_right hhD hq
    dsimp [excess,positivePart]
    apply max_le
    · exact add_nonneg (mul_nonneg hD hq) hpad
    · have hraw := le_max_right (0 : ℝ)
        (Physical.price h point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) h-
          theta+inwardDebit)
      change max 0 _ ≤ _ at hb
      linarith

/-- No second witness or inward fee is charged. The extension is the single
extra rowPad below; the separate outer padding debit is paid by the next result. -/
theorem all_rows_physical_saving_padded {r : Row} (hr : r∈rows)
    {h x D ξ z : ℝ} {point : Point}
    (hh : hLower≤h) (hh' : h≤hUpper) (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : 0≤D) (hDh : D≤h+rowPad)
    (hξ₀ : 0≤ξ) (hξ₁ : ξ≤(rowGamma r.box r.B : ℝ))
    (hz₀ : widthLo≤z) (hz₁ : z≤widthHi) :
    D*point.1*(1/2000000000 : ℝ)-rowPad ≤
      saving r h point.1 point.2 x D ξ z := by
  have hs := Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have ha : (0 : ℝ)<(r.box.uLo : ℝ) := Rat.cast_pos.mpr hs.2.1
  have hd : 0≤point.1 := ha.le.trans hp.1
  have hq := budget_nonnegative hr
  have hq' : (rowBudget r.B : ℝ)≤point.1*((rowBudget r.B : ℝ)/(r.box.uLo : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hp.1 (div_nonneg hq ha.le)
    simpa only [mul_div_cancel₀ _ ha.ne'] using hm
  have hbound := padded_debit hr hh hh' hp hx hD hDh
  have hmin := all_actual_mixed_rows_pays r hr hξ₀ hξ₁ hz₀ hz₁
  have hgain := gain_lower (ξ:=ξ) hr hp hx hz₀ hz₁
  have h₁ := mul_le_mul_of_nonneg_left hgain (mul_nonneg hD hd)
  have h₂ := mul_le_mul_of_nonneg_left hmin (mul_nonneg hD hd)
  have h₃ := mul_le_mul_of_nonneg_left hq' hD
  dsimp [saving]
  nlinarith

/-- The literal normalized scalar price, with the true physical excess divided
by D*d. Its denominator is proved positive in normalized_saving. -/
def normalizedSaving (r : Row) (h d p x D ξ z : ℝ) : ℝ :=
  gain r p x ξ z-excess h d p x D/(D*d)

theorem normalized_saving {r : Row} (hr : r∈rows)
    {h x D ξ z : ℝ} {point : Point}
    (hh : hLower≤h) (hh' : h≤hUpper) (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : 0<D) (hDh : D≤h)
    (hξ₀ : 0≤ξ) (hξ₁ : ξ≤(rowGamma r.box r.B : ℝ))
    (hz₀ : widthLo≤z) (hz₁ : z≤widthHi) :
    (1/2000000000 : ℝ) ≤ normalizedSaving r h point.1 point.2 x D ξ z := by
  have hd : 0<point.1 := lt_of_lt_of_le (by norm_num) (geometry hr hp).2
  have hscale := mul_pos hD hd
  have hb := all_rows_physical_saving hr hh hh' hp hx hD.le hDh hξ₀ hξ₁ hz₀ hz₁
  have he : normalizedSaving r h point.1 point.2 x D ξ z =
      saving r h point.1 point.2 x D ξ z/(D*point.1) := by
    dsimp [normalizedSaving,saving]
    field_simp [hscale.ne']
  rw [he]
  apply (le_div_iff₀ hscale).mpr
  simpa only [mul_comm (1/2000000000 : ℝ)] using hb

theorem actual_padding_small :
    rowPad+paddingDebit+(1/100000000000000 : ℝ)<1/10000000000000 := by
  have hpow : (10 : ℝ)^20<10^(258 : ℕ) :=
    pow_lt_pow_right₀ (by norm_num) (by norm_num)
  have hp := one_div_lt_one_div_of_lt
    (by positivity : (0 : ℝ)<10^(20 : ℕ)) hpow
  have hp' : rowPad<(1/100000000000000000000 : ℝ) := by
    simpa only [rowPad,show (10 : ℝ)^20=100000000000000000000 by norm_num] using hp
  have hs := sourceCost_le_rowPad
  dsimp [paddingDebit]
  linarith

/-- A uniform conservative reserve on the actual supported row band D≥.01.
This proves positivity using the actual operators' scalar price, not the stored
physicalNumerator. The sharper paper reserve uses the original per-ticket D₋. -/
theorem all_rows_uniform_physical_reserve {r : Row} (hr : r∈rows)
    {h x D ξ z : ℝ} {point : Point}
    (hh : hLower≤h) (hh' : h≤hUpper) (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : (1/100 : ℝ)≤D) (hDh : D≤h+rowPad)
    (hξ₀ : 0≤ξ) (hξ₁ : ξ≤(rowGamma r.box r.B : ℝ))
    (hz₀ : widthLo≤z) (hz₁ : z≤widthHi) :
    (1/1000000000000 : ℝ) < saving r h point.1 point.2 x D ξ z-
      paddingDebit-1/100000000000000 := by
  have hD₀ : 0≤D := (by norm_num : (0 : ℝ)≤1/100).trans hD
  have hd := (geometry hr hp).2
  have hscale : (3/800 : ℝ)≤D*point.1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hd)]
  have hb := all_rows_physical_saving_padded hr hh hh' hp hx hD₀ hDh hξ₀ hξ₁ hz₀ hz₁
  linarith [actual_padding_small]

end
end QRH.Cycle092.ActualMixedPrice
#print axioms QRH.Cycle092.ActualMixedPrice.normalized_saving
#print axioms QRH.Cycle092.ActualMixedPrice.all_rows_uniform_physical_reserve
