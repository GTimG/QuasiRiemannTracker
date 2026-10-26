/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RootLedger
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootBinding
set_option autoImplicit false
namespace Cycle153.MarkedRootPrice
/-- Bind the actual fixed initial ledger to the marked source configuration.
This instance consists only of parameter identities. -/
instance fixedRootLedgerBinding : RootLedgerBinding Cycle153.Root.rootLedger where
  q_eq := rfl
  lam_eq := rfl
  B_eq := rfl
  price_eq := rfl
  intercept_eq := rfl
  floor_eq := rfl
  top_eq := rfl
  mesh_eq := rfl
  count_eq := rfl
  window_eq := rfl
  sum_eq := rfl
  comparison_eq := rfl
end Cycle153.MarkedRootPrice
#print axioms Cycle153.MarkedRootPrice.fixedRootLedgerBinding
