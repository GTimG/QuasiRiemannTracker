/- The genuine ROOT density absorption fixes tau before either class or analytic constants.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootReturnAbsorption
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open Filter HeckeFamily Cycle153JointCount
variable (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
variable (eta : Character)(Bnorm cap : ℝ)(hBnorm : 0≤Bnorm)(hcap : 0<cap)
variable (hbudget : ∀d : SuffixDepth 4,(rootHistoryDepth d:ℝ)*250000≤Bnorm)

def actualRootReturnTauAllBudgets : ℝ:=
  Classical.choose (actual_root_forest_scaled_threshold_absorption_all_budgets M H hH eta 250000 Bnorm cap
    (by norm_num) hBnorm hcap hbudget)

theorem actualRootReturnTauAllBudgets_pos : 0<actualRootReturnTauAllBudgets M H hH eta Bnorm cap hBnorm hcap hbudget:=
  (Classical.choose_spec (actual_root_forest_scaled_threshold_absorption_all_budgets M H hH eta 250000 Bnorm cap
    (by norm_num) hBnorm hcap hbudget)).1

theorem actualRootReturnTauAllBudgets_le : actualRootReturnTauAllBudgets M H hH eta Bnorm cap hBnorm hcap hbudget≤cap:=
  (Classical.choose_spec (actual_root_forest_scaled_threshold_absorption_all_budgets M H hH eta 250000 Bnorm cap
    (by norm_num) hBnorm hcap hbudget)).2.1

def actualRootReturnEventAllBudgets (N : ℕ)(Kclass : ℝ)(hclass : 0≤Kclass)(Kreturn : ℝ)(hreturn : 0≤Kreturn):=
  (Classical.choose_spec (actual_root_forest_scaled_threshold_absorption_all_budgets M H hH eta 250000 Bnorm cap
    (by norm_num) hBnorm hcap hbudget)).2.2 N Kclass hclass Kreturn hreturn

def actualRootReturnThresholdAllBudgets (N : ℕ)(Kclass : ℝ)(hclass : 0≤Kclass)(Kreturn : ℝ)(hreturn : 0≤Kreturn) : ℝ:=
  Classical.choose (eventually_atTop.mp (actualRootReturnEventAllBudgets M H hH eta Bnorm cap hBnorm hcap hbudget N Kclass hclass Kreturn hreturn))

def actualRootReturnAfterAllBudgets (N : ℕ)(Kclass : ℝ)(hclass : 0≤Kclass)(Kreturn : ℝ)(hreturn : 0≤Kreturn)
    (Z : ℝ)(hZ : actualRootReturnThresholdAllBudgets M H hH eta Bnorm cap hBnorm hcap hbudget N Kclass hclass Kreturn hreturn≤Z):=
  Classical.choose_spec (eventually_atTop.mp (actualRootReturnEventAllBudgets M H hH eta Bnorm cap hBnorm hcap hbudget N Kclass hclass Kreturn hreturn)) Z hZ
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actualRootReturnAfterAllBudgets
