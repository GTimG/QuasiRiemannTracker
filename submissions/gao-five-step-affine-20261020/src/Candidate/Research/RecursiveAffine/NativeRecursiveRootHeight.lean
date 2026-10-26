/- The root density height precedes the original cardinality and every source schedule.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootReturnThresholdAllBudgets
import Candidate.Research.RecursiveAffine.SourceContextFactory
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RootLowSchedule
noncomputable section
open HeckeFamily Cycle153Reachable Cycle153SourceSchedule Cycle153JointCount
variable (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
variable (eta : Character)

theorem actual_recursive_root_norm_nonneg : 0≤returnedNormCap 250000:=by
  exact le_trans (by norm_num) (returnedNormCap_large (by norm_num))

theorem actual_recursive_root_history_budget (d : SuffixDepth 4) :
    (rootHistoryDepth d:ℝ)*250000≤returnedNormCap 250000:=by
  have hd:=suffixOffset_lt 4 d
  have hn : rootHistoryDepth d≤4:=by unfold rootHistoryDepth;omega
  have hc : (rootHistoryDepth d:ℝ)≤4:=by exact_mod_cast hn
  norm_num only [returnedNormCap]
  linarith only [hc]

/-- This real is independent of the original slot type, dyad-box budget,
class bound and analytic return constants. They enter only later thresholds. -/
def actualRecursiveRootTau : ℝ:=actualRootReturnTauAllBudgets M H hH eta
  (returnedNormCap 250000) 1 actual_recursive_root_norm_nonneg (by norm_num)
  actual_recursive_root_history_budget

theorem actualRecursiveRootTau_pos : 0<actualRecursiveRootTau M H hH eta:=
  actualRootReturnTauAllBudgets_pos M H hH eta (returnedNormCap 250000) 1
    actual_recursive_root_norm_nonneg (by norm_num) actual_recursive_root_history_budget

theorem actualRecursiveRootTau_le_one : actualRecursiveRootTau M H hH eta≤1:=
  actualRootReturnTauAllBudgets_le M H hH eta (returnedNormCap 250000) 1
    actual_recursive_root_norm_nonneg (by norm_num) actual_recursive_root_history_budget
end
end OAI.SevenEighths.Cycle153RootLowSchedule
#print axioms OAI.SevenEighths.Cycle153RootLowSchedule.actualRecursiveRootTau_pos
#print axioms OAI.SevenEighths.Cycle153RootLowSchedule.actual_recursive_root_history_budget
