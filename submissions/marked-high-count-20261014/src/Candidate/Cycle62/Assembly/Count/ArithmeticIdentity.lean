import Candidate.Cycle62.Physical.WitnessGeometry
import Candidate.Cycle25.Assembly.Count.Endpoint

namespace Cycle62.Assembly.Count
noncomputable section
open Arithmetic.Bernstein
open OAI.SevenEighths.Cycle25DetectorRowCount

theorem cutoff_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    cutoff delta p κ = Physical.witnessCutoff κ delta p := by
  simp only [cutoff, Physical.witnessCutoff, V, rowDen, Physical.coefficient_eq_old hk]

theorem rowCount_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    rowCount delta p κ = countingR κ delta p := by
  simp only [rowCount, countingR, V, rowDen, Physical.coefficient_eq_old hk]
end
end Cycle62.Assembly.Count
