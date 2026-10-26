import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Arithmetic.Bernstein.Feedback
import Candidate.Cycle25.Assembly.Count.Crossing

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Physical_WitnessGeometry : Cycle63.AffineLedger := Cycle153.Root.rootLedger


namespace Cycle153Endpoint.Physical

open Arithmetic Arithmetic.Bernstein

noncomputable section

-- These predecessor results are variable-κ arithmetic, with no moment premise.

theorem coefficient_eq_old {κ p : ℝ} (hk : 7 / 10 ≤ κ) :
    countingCoefficient κ p = OAI.SevenEighths.Cycle25DetectorRowCount.coefficient p κ := by
  simpa only [OAI.SevenEighths.Cycle25DetectorRowCount.coefficient,
    OAI.SevenEighths.Cycle25DetectorRowCount.primeWeight,
    OAI.SevenEighths.Cycle25DetectorRowCount.denominator,
    OAI.SevenEighths.Cycle25DetectorRowCount.b, mul_div_assoc] using
      canonical_counting_formula hk

end

end Cycle153Endpoint.Physical
