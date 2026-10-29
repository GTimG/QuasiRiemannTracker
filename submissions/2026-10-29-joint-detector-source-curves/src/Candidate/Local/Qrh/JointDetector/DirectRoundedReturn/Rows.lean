/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.DirectRoundedReturn.Cover
import Candidate.Local.Qrh.JointDetector.DirectRoundedReturn.Conductor
import Candidate.Local.Qrh.JointDetector.DirectRoundedReturn.Geometry
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
namespace Qrh.JointDetector.DirectRoundedReturn
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
noncomputable section
local instance : Geometry.Parameters := parameters
local instance : CountScheme := finalCountScheme
namespace FinalEdges
abbrev bs : List Branch := GenericCount.admittedBranches

theorem edge_bound (e : Edge) {δ p : ℝ}
 (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
 rowAt bs kappa (edgeD e) (edgeC e) δ p ≤ theta-reserve := by
 have hh := (closed_envelope_return_cover e hδ hp).le
 unfold rowAt
 change Ebase (edgeD e) (edgeC e) δ p + 3*edgeD e*
  (@GenericCount.envelope finalCountScheme kappa δ p)/4 ≤ _
 nlinarith only [hh]

theorem generic_row_eq (bs : List Branch) (κ d C δ p : ℝ) :
 Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowAt bs κ d C δ p = rowAt bs κ d C δ p := by
 unfold Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowAt rowAt Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.Ebase Ebase
 simp only [Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.h,Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.y,Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.ell,
  parameters_h,parameters_y,parameters_ell]

theorem reserve_le : theta-reserve ≤ theta-Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowFee := by
 norm_num [theta,reserve,Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowFee]
end FinalEdges

theorem old_rows {d δ p : ℝ} (hd : d ∈ Set.Icc d0 dm)
 (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
 Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowAt GenericCount.admittedBranches kappa d
  (Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.oldCapacityAt kappa d) δ p ≤ theta-Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowFee := by
 refine le_trans ?_ FinalEdges.reserve_le
 rw [FinalEdges.generic_row_eq]
 change oldExponent FinalEdges.bs d δ p ≤ _
 apply old_interval_bound FinalEdges.bs hd hδ hp
 · simpa only [oldExponent,oldCapacityAt,edgeD,
     edgeC,oldCapacity] using FinalEdges.edge_bound .oldSmall hδ hp
 · simpa only [oldExponent,oldCapacityAt,edgeD,
     edgeC,oldCapacity] using FinalEdges.edge_bound .oldSwitch hδ hp

theorem new_rows {d δ p : ℝ} (hd : d ∈ Set.Icc dm dp)
 (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
 Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowAt GenericCount.admittedBranches kappa d
  (min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)) δ p ≤
   theta-Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.rowFee := by
 refine le_trans ?_ FinalEdges.reserve_le
 rw [FinalEdges.generic_row_eq]
 change newExponent FinalEdges.bs d δ p ≤ _
 apply new_interval_bound FinalEdges.bs hd hδ hp
 · simpa only [newExponent,edgeD,edgeC] using
     FinalEdges.edge_bound .newSwitch hδ hp
 · simpa only [newExponent,edgeD,edgeC] using
     FinalEdges.edge_bound .newTop hδ hp
end
end Qrh.JointDetector.DirectRoundedReturn
#print axioms Qrh.JointDetector.DirectRoundedReturn.old_rows
#print axioms Qrh.JointDetector.DirectRoundedReturn.new_rows
