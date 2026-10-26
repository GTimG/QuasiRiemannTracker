/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Return.CountingGap
import Submissions.hailey_collet_1252270103.Record12518109Return.FiniteEnvelope
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.Endpoint
set_option autoImplicit false
namespace QRH.Record12518109Return
noncomputable section
open OAI.SevenEighths
theorem countingR_eq_actual {κ δ p : ℝ} (hk : 7/10 ≤ κ) :
    countingR κ δ p = Cycle25DetectorRowCount.rowCount δ p κ := by
  have hc : countingCoefficient κ p = Cycle25DetectorRowCount.coefficient p κ := by
    rw [canonical_counting_formula hk]
    unfold Cycle25DetectorRowCount.coefficient Cycle25DetectorRowCount.primeWeight
      Cycle25DetectorRowCount.denominator Cycle25DetectorRowCount.b
    congr 1 <;> ring
  unfold countingR rowDen Cycle25DetectorRowCount.rowCount Cycle25DetectorRowCount.V
  rw [hc]
def envelope (bs : List Branch) (κ δ p : ℝ) : ℝ :=
  finiteEnvelope countingR bs κ δ p
theorem envelope_gap (bs : List Branch) {a κ δ p : ℝ}
    (ha : 7/10 ≤ a) (hak : a ≤ κ) (hδ : 0 ≤ δ ∧ δ ≤ 5/6)
    (hp : 0 ≤ p ∧ p ≤ 1/2) :
    envelope bs κ δ p-envelope bs a δ p ≤ (5/12)*((κ-a)/18) := by
  apply finiteEnvelope_gap countingR bs (by positivity)
  exact row_gap ha hak hδ hp
end
end QRH.Record12518109Return
#print axioms QRH.Record12518109Return.countingR_eq_actual
#print axioms QRH.Record12518109Return.envelope_gap
