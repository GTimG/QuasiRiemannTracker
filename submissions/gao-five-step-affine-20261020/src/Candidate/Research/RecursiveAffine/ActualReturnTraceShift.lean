/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualReturnShift
import Candidate.Research.RecursiveAffine.ReachableNode

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily Cycle153SourceReturn Cycle153RegionalLow

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}{N : ReachableNode C j}

/-- An actual source shell fee changes terminal count-form exponents
and their explicit native loss only. Every physical node, original raw
edge weight, missing radical, capacity, global coordinate, multiplier,
and literal terminal scale/volume/amplifier survives unchanged. -/
def ActualPathTrace.shiftTerminal {representedBase representedUnit : ℝ}
    {F : SuffixFamily (hH:=hH) j.val (4-j.val) C.etaSeed representedBase C.Bnorm C.Tz
      N.presentation.mult}{d : SuffixDepth (4-j.val)}{p : F.Prefix d}
    (trace : ActualPathTrace hH N representedUnit F d p)(shift : ℝ) :
    ActualPathTrace hH N representedUnit (shiftedReturnedForest F shift) d p :=
  { trace with }

end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.ActualPathTrace.shiftTerminal
