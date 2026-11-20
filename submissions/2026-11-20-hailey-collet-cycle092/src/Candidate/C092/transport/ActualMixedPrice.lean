/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The physical Q1/Q2 interface below uses the original price, true contact
coefficients and the inherited Collet/Levy/Gao/Bebel source and witness prices.
The finite proofs in TopActual and MixedChecks supply all their scalar bounds. -/
import Candidate.C092.transport.TopActual
import Candidate.C092.transport.MixedChecks
import Candidate.C092.transport.DirectPairedAdmission

/-! Physical interpretation of every Q mixed terminal.  The count-deficit
faces are the directed P14 faces; the density, amplitude, contact and original
capped-capacity price are evaluated at the live point.  This is a scalar
exponent theorem, not an assertion of the still-needed analytic count/moment
and packet decomposition for the selected Mellin integrand. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
namespace QRH.Cycle092.ActualMixedPrice
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
open QRH.ContactCertificate QRH.PhysicalCertificate QRH.Coverage
noncomputable section

/-- Exact geometry checks, independent of stored terminal prices. -/
def geometryCheck (r : Row) : Bool := decide
  (Box.Included r.box Direct.pairedAdmissionBox ∧ (3/8 : ℚ) ≤ r.box.uLo)

set_option maxHeartbeats 0 in
theorem all_geometry_checked : rows.all geometryCheck = true := by
  simp only [rows,List.all_append,Bool.and_eq_true]
  repeat' constructor
  all_goals decide +kernel

theorem geometry {r : Row} (hr : r∈rows) {point : Point}
    (hp : r.box.Contains point) :
    Direct.pairedAdmissionBox.Contains point ∧ (3/8 : ℝ) ≤ point.1 := by
  have hc := List.all_eq_true.mp all_geometry_checked r hr
  simp only [geometryCheck,decide_eq_true_eq] at hc
  refine ⟨Box.contains_of_included hc.1 hp, ?_⟩
  have hlo : (3/8 : ℝ) ≤ (r.box.uLo : ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr hc.2)
  exact hlo.trans hp.1

/-- All ten actual E29 guards hold on every mixed row and at the actual
algebraic contact, including all closed box boundaries. -/
theorem full_admission {r : Row} (hr : r∈rows) {point : Point}
    (hp : r.box.Contains point) {x : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval x) (i : Fin 10) :
    (1/1000 : ℝ) ≤ Direct.pairedGuard i point.1 point.2
      (g0 (wValue x)) (g1 (wValue x)) := by
  have h := Physical.actual_contact_bounds hx
  exact Direct.paired_admission_real (geometry hr hp).1 h.1 h.2.1 h.2.2.1 h.2.2.2 i

/-- The actual source width, before replacing its contact by directed ends. -/
def sourceWidth (x z : ℝ) : ℝ :=
  g1 (wValue x)*z-g0 (wValue x)/2+sourceGain z

theorem beta_le_sourceWidth {x z : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval x) (hz : 0≤z) :
    beta z ≤ sourceWidth x z := by
  have h0 := g0_receipt_sound hx
  have h1 := g1_receipt_sound hx
  have hm := mul_le_mul_of_nonneg_right h1.1 hz
  dsimp [beta,betaSlope,betaIntercept,sourceWidth]
  linarith [h0.2]

/-- The three original directed faces in Q2, with all offsets retained. -/
def penalty (r : Row) (ξ z : ℝ) : ℝ :=
  witnessPenalty (rowKLower r.box) (rowKUpper r.box)
    (-(rowKUpper r.box : ℝ)*(ξ+3*witnessCollar))
    (((rowV r.box : ℝ)/r.box.uHi)*max 0
      (ξ-(rowGamma r.box r.B : ℝ)/65536-3*witnessCollar))
    ((rowM r.box : ℝ)+witnessCollar) z

/-- Live amplitude and true source gain; the collar is paid once. -/
def gain (r : Row) (p x ξ z : ℝ) : ℝ :=
  p*sourceWidth x z+penalty r ξ z/2-p*witnessCollar/2

/-- The actual physical Q1 excess, including Q2's allocated inward fee. -/
def excess (h d p x D : ℝ) : ℝ :=
  positivePart (Physical.price h d p (g0 (wValue x)) (g1 (wValue x)) D-
    theta+inwardDebit)

/-- The physical Z-exponent saving: Q2's row gain minus the actual Q1 debit.
The conversion is by the live row conductor D and density d, not the box ends. -/
def saving (r : Row) (h d p x D ξ z : ℝ) : ℝ :=
  D*d*gain r p x ξ z-excess h d p x D

theorem gain_lower {r : Row} (hr : r∈rows) {point : Point}
    (hp : r.box.Contains point) {x ξ z : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hz₀ : widthLo≤z) (hz₁ : z≤widthHi) :
    actualWitnessPrice r.box r.B ξ z+(rowBudget r.B : ℝ)/(r.box.uLo : ℝ) ≤
      gain r point.2 x ξ z := by
  have hs := Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have hg := Top.point_guards hs hp
  have hb := beta_positive hz₀ hz₁
  have hz : 0≤z := (by norm_num [widthLo] : (0 : ℝ)≤widthLo).trans hz₀
  have hw := beta_le_sourceWidth hx hz
  have hβ := mul_le_mul_of_nonneg_right hp.2.2.1 (by linarith : 0≤beta z)
  have hw' := mul_le_mul_of_nonneg_left hw hg.2.2.1
  have hfee := mul_le_mul_of_nonneg_right hp.2.2.2
    (show 0≤witnessCollar/2 by norm_num [witnessCollar])
  dsimp [actualWitnessPrice,witnessPrice,rowFee,gain,penalty]
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  dsimp [witnessCollar] at hfee ⊢
  linarith

theorem budget_nonnegative {r : Row} (hr : r∈rows) : 0≤(rowBudget r.B : ℝ) := by
  have hs := Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  rw [rowBudget_cast hs.1]
  have hB : (0 : ℝ)≤(r.B : ℝ) := Rat.cast_nonneg.mpr hs.1
  exact div_nonneg (add_nonneg hB allowances_pos.2.2.2.2.le)
    (by norm_num [hLower])

/-- All 9,681 original mixed boxes pay their actual capped-capacity price,
for every real offset and both sides of the source seam. No stored margin,
contact approximation, or assumed top-excess bound is a premise. -/
theorem all_rows_physical_saving {r : Row} (hr : r∈rows)
    {h x D ξ z : ℝ} {point : Point}
    (hh : hLower≤h) (hh' : h≤hUpper) (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : 0≤D) (hDh : D≤h)
    (hξ₀ : 0≤ξ) (hξ₁ : ξ≤(rowGamma r.box r.B : ℝ))
    (hz₀ : widthLo≤z) (hz₁ : z≤widthHi) :
    D*point.1*(1/2000000000 : ℝ) ≤ saving r h point.1 point.2 x D ξ z := by
  have hs := Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have ha : (0 : ℝ)<(r.box.uLo : ℝ) := Rat.cast_pos.mpr hs.2.1
  have hd : 0≤point.1 := ha.le.trans hp.1
  have hq := budget_nonnegative hr
  have hq' : (rowBudget r.B : ℝ)≤point.1*((rowBudget r.B : ℝ)/(r.box.uLo : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hp.1 (div_nonneg hq ha.le)
    simpa only [mul_div_cancel₀ _ ha.ne'] using hm
  have hbound := Top.every_row_normalized_debit hr hh hh' hp hx hD hDh
  have hcast : (rowBudget r.B : ℝ)=Top.debit r := rowBudget_cast hs.1
  rw [← hcast] at hbound
  have hmin := all_actual_mixed_rows_pays r hr hξ₀ hξ₁ hz₀ hz₁
  have hgain := gain_lower (ξ:=ξ) hr hp hx hz₀ hz₁
  have h₁ := mul_le_mul_of_nonneg_left hgain (mul_nonneg hD hd)
  have h₂ := mul_le_mul_of_nonneg_left hmin (mul_nonneg hD hd)
  have h₃ := mul_le_mul_of_nonneg_left hq' hD
  dsimp [saving,excess]
  nlinarith

end
end QRH.Cycle092.ActualMixedPrice
#print axioms QRH.Cycle092.ActualMixedPrice.full_admission
#print axioms QRH.Cycle092.ActualMixedPrice.all_rows_physical_saving
