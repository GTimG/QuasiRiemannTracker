/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootCells
namespace Cycle153.MarkedRootPrice
/-- Configuration equalities for the fixed initial root ledger. These bind
native source/window APIs; they contain no count or energy assertion. -/
class RootLedgerBinding (L : Cycle63.AffineLedger) : Prop where
  q_eq : L.q=q
  lam_eq : L.lam=lambda
  B_eq : L.B=B
  price_eq : L.price=price
  intercept_eq : L.intercept=intercept
  floor_eq : L.slotFloor=Cycle63.Optimization.slotFloor
  top_eq : L.slotTop=top
  mesh_eq : L.cellMesh=Cycle63.Optimization.cellMesh
  count_eq : L.cellCount=cellCount
  window_eq : L.windowBottom=81/200
  sum_eq : L.sumBottom=81/100
  comparison_eq : L.comparisonLength=(fun _ _ _=>1/4)
end Cycle153.MarkedRootPrice
