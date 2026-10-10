import WeightedQRH.ExponentCertificate
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount
import OAI.NumberTheory.DirichletL.Endpoint

namespace WeightedQRH
noncomputable section
open OAI.SevenEighths

/-- The new certificate uses exactly the original balanced count, in x=q/δ coordinates. -/
theorem balanced_count_identity {δ x : ℝ} (hJ : countDen δ x ≠ 0) :
    Endpoint.balancedRowCount δ (1 / 2 - x) = rowCount δ x := by
  have hden : Endpoint.balanceDenominator δ (1 / 2 - x) = countDen δ x := by
    unfold Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight countDen countD countP
    ring
  unfold Endpoint.balancedRowCount Endpoint.balancedCutoff
  rw [hden]
  have hp : Endpoint.primeWeight (1 / 2 - x) = countP x := by
    unfold Endpoint.primeWeight countP
    ring
  rw [hp, rowCount_formula hJ]
  ring

theorem adaptive_count_identity {δ q ε εm R ν : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 3 / 4) (hq0 : 0 ≤ q) (hq1 : q ≤ δ / 2) :
    ProbeHighRowFamily.adaptiveRowExponent δ q 0 ε εm R ν =
      rowCount δ (q / δ) + (159 * ε + εm + R + 7 * ν) := by
  have hx0 : 0 ≤ q / δ := div_nonneg hq0 hδ0.le
  have hx1 : q / δ ≤ 1 / 2 := (div_le_iff₀ hδ0).mpr (by linarith)
  have hδ : δ ≤ 5 / 6 := by linarith
  simp only [ProbeHighRowFamily.adaptiveRowExponent, if_pos hδ, zero_div, add_zero]
  rw [balanced_count_identity (countDen_pos hδ0.le hδ1 hx0 hx1).ne']
  ring

/-- A simple density bound sufficient for the intermediate row range. -/
theorem rowCount_density_bound {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    rowCount δ x ≤ 1 - 2 * δ / 3 := by
  have hJ := countDen_pos hδ0 hδ1 hx0 hx1
  have ha : 0 ≤ (5 / 6 : ℝ) - δ := by linarith
  have hp : 0 ≤ countP x := by
    unfold countP
    apply mul_nonneg <;> linarith
  have hdp : 0 ≤ 2 * countD x - 3 * countP x := by
    have hxx := mul_nonneg hx0 (sub_nonneg.mpr hx1)
    unfold countD countP
    nlinarith
  have hprod := mul_nonneg hδ0 (add_nonneg (mul_nonneg ha hdp) (mul_nonneg (by linarith : 0 ≤ 2 * δ) hp))
  rw [rowCount_formula hJ.ne']
  have hd : (5 / 6 - δ) * δ * countP x / (2 * countDen δ x) ≤ δ / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * countDen δ x)).mpr
    unfold countDen
    nlinarith [hprod]
  linarith

end
end WeightedQRH
