import Candidate.Cycle63.Assembly.Geometry
import Candidate.Cycle63.Physical.WitnessGeometry

namespace Cycle63.Assembly.Count
noncomputable section
open Arithmetic

/-- The new exact slot total supplies the generic whole-slot detector selector. -/
theorem count_slot_supply : (7/37:ℝ)*(7/8)≤ell := by norm_num [ell, theta]
theorem ell_pos : 0<ell := Arithmetic.ell_pos

end
end Cycle63.Assembly.Count
