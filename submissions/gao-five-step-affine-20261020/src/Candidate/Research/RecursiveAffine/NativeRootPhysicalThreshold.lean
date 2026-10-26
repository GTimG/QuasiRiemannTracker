/- The genuine native root physical operator is chosen before the moving source.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootPhysicalReceipt
import Candidate.Research.RecursiveAffine.SourceContextFee
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open Filter HeckeFamily Cycle153SourceSchedule Cycle153Reachable
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
noncomputable local instance rootPhysicalThresholdLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

def actualRootPhysicalConstant (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ) : ℝ:=
  Classical.choose (eventual_actual_root_physical_receipt (alpha:=alpha) (Current:=alpha)
    (hH:=hH) Nrow 3 (postDictionaryRate Bnorm budget) (postDictionaryRate Bnorm budget)
    (by norm_num) (postDictionaryRate_budgets hB budget).1.le (postDictionaryRate_budgets hB budget).1)

theorem actualRootPhysicalConstant_pos (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ) :
    0<actualRootPhysicalConstant (alpha:=alpha) hH Bnorm hB budget Nrow:=
  (Classical.choose_spec (eventual_actual_root_physical_receipt (alpha:=alpha) (Current:=alpha)
    (hH:=hH) Nrow 3 (postDictionaryRate Bnorm budget) (postDictionaryRate Bnorm budget)
    (by norm_num) (postDictionaryRate_budgets hB budget).1.le (postDictionaryRate_budgets hB budget).1)).1

def actualRootPhysicalEvent (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ):=
  (Classical.choose_spec (eventual_actual_root_physical_receipt (alpha:=alpha) (Current:=alpha)
    (hH:=hH) Nrow 3 (postDictionaryRate Bnorm budget) (postDictionaryRate Bnorm budget)
    (by norm_num) (postDictionaryRate_budgets hB budget).1.le (postDictionaryRate_budgets hB budget).1)).2

def actualRootPhysicalThreshold (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ) : ℝ:=
  Classical.choose (eventually_atTop.mp (actualRootPhysicalEvent (alpha:=alpha) hH Bnorm hB budget Nrow))

def actualRootPhysicalAfter (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ)
    (Z : ℝ)(hZ : actualRootPhysicalThreshold (alpha:=alpha) hH Bnorm hB budget Nrow≤Z):=
  Classical.choose_spec (eventually_atTop.mp (actualRootPhysicalEvent (alpha:=alpha) hH Bnorm hB budget Nrow)) Z hZ
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actualRootPhysicalAfter
