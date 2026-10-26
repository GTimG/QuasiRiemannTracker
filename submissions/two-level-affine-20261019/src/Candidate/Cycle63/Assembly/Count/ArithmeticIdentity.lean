import Candidate.Cycle63.Physical.WitnessGeometry
import Candidate.Cycle25.Assembly.Count.Endpoint

namespace Cycle63.Assembly.Count
noncomputable section
open Arithmetic.Bernstein
open OAI.SevenEighths.Cycle25DetectorRowCount

theorem rowCount_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    rowCount delta p κ = countingROld κ delta p := by
  simp only [rowCount, countingROld, V, rowDen, Physical.coefficient_eq_old hk]
end
end Cycle63.Assembly.Count
