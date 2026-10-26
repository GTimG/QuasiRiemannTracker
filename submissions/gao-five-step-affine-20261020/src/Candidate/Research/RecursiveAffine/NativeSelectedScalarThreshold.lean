/- Fixed pre-source thresholds for the genuine native scalar/mask producers. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedScalarUniform
import Candidate.Research.RecursiveAffine.NativeAllRowMasks

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open Filter


def actualSelectedScalarThreshold (budget : ℕ)(epsV : ℝ)(hepsV : 0<epsV) : ℝ:=
  Classical.choose (eventually_atTop.mp (eventual_actual_selected_scalar_payment_uniform budget epsV hepsV))

/-- This is the genuine source scalar theorem after its fixed threshold.
The threshold depends only on the fixed ledger/cardinality/error, before
any character, weighted source, native label, ray or physical row. -/
def actualSelectedScalarAfter (budget : ℕ)(epsV : ℝ)(hepsV : 0<epsV)
    (Z : ℝ)(hZ : actualSelectedScalarThreshold budget epsV hepsV≤Z) :=
  Classical.choose_spec (eventually_atTop.mp (eventual_actual_selected_scalar_payment_uniform budget epsV hepsV)) Z hZ

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.actualSelectedScalarAfter
