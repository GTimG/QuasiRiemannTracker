import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Geometry
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Physical.WitnessGeometry

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Count_Geometry : Cycle63.AffineLedger := Cycle153.Root.rootLedger


namespace Cycle153Endpoint.Assembly.Count
noncomputable section
open Arithmetic

/-- The new exact slot total supplies the generic whole-slot detector selector. -/
theorem count_slot_supply : (7/37:ℝ)*(7/8)≤ell := by norm_num [ell, theta]
theorem ell_pos : 0<ell := Arithmetic.ell_pos

end
end Cycle153Endpoint.Assembly.Count
