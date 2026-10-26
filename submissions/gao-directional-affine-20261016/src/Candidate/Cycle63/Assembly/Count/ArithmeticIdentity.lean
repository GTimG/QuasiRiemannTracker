/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Candidate.Cycle63.Physical.WitnessGeometry
import Candidate.Cycle25.Assembly.Count.Endpoint

                                       
                                      

namespace Cycle63.Assembly.Count
noncomputable section
open Arithmetic.Bernstein
open OAI.SevenEighths.Cycle25DetectorRowCount

theorem cutoff_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    cutoff delta p κ = Physical.witnessCutoff κ delta p := by
  simp only [cutoff, Physical.witnessCutoff, V, rowDen, Physical.coefficient_eq_old hk]

theorem rowCount_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    rowCount delta p κ = countingR0 κ delta p := by
  simp only [rowCount, countingR0, V, rowDen, Physical.coefficient_eq_old hk]
end
end Cycle63.Assembly.Count

