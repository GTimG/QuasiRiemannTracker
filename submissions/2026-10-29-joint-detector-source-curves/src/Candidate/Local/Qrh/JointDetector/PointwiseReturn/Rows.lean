/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Cover
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Conductor
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Geometry
import Submissions.sil_density_split_20261026.ReturnD.Schedule
namespace Qrh.JointDetector.PointwiseReturn
open QRH.Record1252270103Return
open QRH.SilDensitySplit.Return.GenericArithmetic
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
 QRH.SilDensitySplit.Return.GenericArithmetic.rowAt bs κ d C δ p = rowAt bs κ d C δ p := by
 unfold QRH.SilDensitySplit.Return.GenericArithmetic.rowAt rowAt QRH.SilDensitySplit.Return.GenericArithmetic.Ebase Ebase
 simp only [QRH.SilDensitySplit.Return.GenericArithmetic.h,QRH.SilDensitySplit.Return.GenericArithmetic.y,QRH.SilDensitySplit.Return.GenericArithmetic.ell,
  parameters_h,parameters_y,parameters_ell]

theorem reserve_le : theta-reserve ≤ theta-QRH.SilDensitySplit.Return.GenericArithmetic.rowFee := by
 norm_num [theta,reserve,QRH.SilDensitySplit.Return.GenericArithmetic.rowFee]
end FinalEdges

theorem old_rows {d δ p : ℝ} (hd : d ∈ Set.Icc d0 dm)
 (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
 QRH.SilDensitySplit.Return.GenericArithmetic.rowAt GenericCount.admittedBranches kappa d
  (QRH.SilDensitySplit.Return.GenericArithmetic.oldCapacityAt kappa d) δ p ≤ theta-QRH.SilDensitySplit.Return.GenericArithmetic.rowFee := by
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
 QRH.SilDensitySplit.Return.GenericArithmetic.rowAt GenericCount.admittedBranches kappa d
  (min (numeratorCap*d) ((2*y-(2-physicalB)*d)/physicalLambda)) δ p ≤
   theta-QRH.SilDensitySplit.Return.GenericArithmetic.rowFee := by
 refine le_trans ?_ FinalEdges.reserve_le
 rw [FinalEdges.generic_row_eq]
 change newExponent FinalEdges.bs d δ p ≤ _
 apply new_interval_bound FinalEdges.bs hd hδ hp
 · simpa only [newExponent,edgeD,edgeC] using
     FinalEdges.edge_bound .newSwitch hδ hp
 · simpa only [newExponent,edgeD,edgeC] using
     FinalEdges.edge_bound .newTop hδ hp
end
end Qrh.JointDetector.PointwiseReturn
#print axioms Qrh.JointDetector.PointwiseReturn.old_rows
#print axioms Qrh.JointDetector.PointwiseReturn.new_rows
