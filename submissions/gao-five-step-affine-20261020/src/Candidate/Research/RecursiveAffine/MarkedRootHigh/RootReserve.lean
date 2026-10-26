/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootDefinitions
set_option autoImplicit false
namespace Cycle153.MarkedRootPrice
noncomputable section
open Cycle63.Optimization

theorem markedLoss_pos : 0 < markedLoss := markedLossAt_pos top_pos.le

theorem marked_high_reserve {b d : ℝ} (hb : b∈Set.Icc bottom top) (hd : d∈Set.Icc q (2/3)) :
    lowReserve+markedLoss≤highMainReserve b d+commonRateAt d*suppliedAt b :=
  (ledger_channels hd hb).1

theorem unmarked_upper_high_reserve {b d : ℝ} (hb : b∈Set.Icc bottom top) (hd : d∈Set.Icc (2/3) (3/4)) :
    lowReserve+markedLoss≤highMainReserve b d := ledger_unmarked hd hb
end
end Cycle153.MarkedRootPrice

#print axioms Cycle153.MarkedRootPrice.marked_high_reserve
#print axioms Cycle153.MarkedRootPrice.unmarked_upper_high_reserve
