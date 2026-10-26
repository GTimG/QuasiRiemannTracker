/- The true all-row root arithmetic sources share one pre-source cutoff. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootAllRowSourceFacts
import Candidate.Research.RecursiveAffine.NativeAllRowMasks
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open Filter Cycle153ActualSourceGates
noncomputable local instance rootAllRowThresholdLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

def actualRootAllRowEvent (budget : ℕ):=
  (eventual_actual_root_all_row_source_facts budget).and (eventual_actual_selected_all_row_masks budget)
def actualRootAllRowThreshold (budget : ℕ) : ℝ:=
  Classical.choose (eventually_atTop.mp (actualRootAllRowEvent budget))
def actualRootAllRowAfter (budget : ℕ)(Z : ℝ)(hZ : actualRootAllRowThreshold budget≤Z):=
  Classical.choose_spec (eventually_atTop.mp (actualRootAllRowEvent budget)) Z hZ
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actualRootAllRowAfter
