import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Physical.WitnessGeometry
import Candidate.Cycle25.Assembly.Count.Endpoint

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Count_ArithmeticIdentity : Cycle63.AffineLedger := Cycle153.Root.rootLedger


namespace Cycle153Endpoint.Assembly.Count
noncomputable section
open Arithmetic.Bernstein
open OAI.SevenEighths.Cycle25DetectorRowCount

theorem rowCount_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    rowCount delta p κ = countingROld κ delta p := by
  simp only [rowCount, countingROld, V, rowDen, Physical.coefficient_eq_old hk]
end
end Cycle153Endpoint.Assembly.Count
