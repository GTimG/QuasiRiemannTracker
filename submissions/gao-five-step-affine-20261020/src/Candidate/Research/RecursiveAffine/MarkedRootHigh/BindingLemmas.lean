/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootBinding
namespace Cycle153.MarkedRootPrice
noncomputable section
variable [L : Cycle63.AffineLedger] [RootLedgerBinding L]

theorem affine_totalA_eq (b : ℝ) : Cycle63.AffineLedger.totalA b=totalA b := by
  simp only [Cycle63.AffineLedger.totalA,Cycle63.Optimization.planeTotalLength,totalA,
    RootLedgerBinding.lam_eq,RootLedgerBinding.B_eq,RootLedgerBinding.mesh_eq]

theorem affine_amp_eq (b : ℝ) : Cycle63.AffineLedger.amp b=amp b := by
  simp only [Cycle63.AffineLedger.amp,Cycle63.AffineLedger.Ka,Cycle63.AffineLedger.regionGap,
    Cycle63.Optimization.planeGap,amp,Cycle63.Optimization.planeAmplifier,
    RootLedgerBinding.q_eq,RootLedgerBinding.lam_eq,RootLedgerBinding.B_eq,
    RootLedgerBinding.price_eq,RootLedgerBinding.intercept_eq]

theorem affine_cellUpper_eq (j : ℕ) : Cycle63.AffineLedger.cellUpper j=cellUpper j := by
  simp only [Cycle63.AffineLedger.cellUpper,cellUpper,Cycle63.Arithmetic.cellUpper,
    RootLedgerBinding.floor_eq,RootLedgerBinding.mesh_eq]

theorem affine_originalCell_eq (b : ℝ) : Cycle63.AffineLedger.originalCell b=originalCell b := by
  simp only [Cycle63.AffineLedger.originalCell,originalCell,Cycle63.Moment.originalCell,
    RootLedgerBinding.floor_eq,RootLedgerBinding.mesh_eq]
end
end Cycle153.MarkedRootPrice

#print axioms Cycle153.MarkedRootPrice.affine_amp_eq
