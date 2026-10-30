import Candidate.ReturnB.Geometry
/- Adapted 2026-10-24 for Subhanjan Das, AI-assisted with OpenAI Codex.
Original Hailey Collet/Mark Lewko notices and Apache-2.0 license retained. -/
/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact finite envelope rows instantiated in the generic physical geometry. -/
import Candidate.ReturnB.EdgeCover
import Candidate.ReturnB.Conductor
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.TransportInstances
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Das.QRH.ReturnB
open QRH.LewkoStage2Return
noncomputable section
local instance : Geometry.Parameters := Das.QRH.ReturnB.parameters
local instance : Geometry.Bounds := Das.QRH.ReturnB.bounds
local instance : CountScheme := finalCountScheme
namespace FinalRows
open DasStageBFinite
abbrev bs : List Branch := GenericCount.admittedBranches

theorem edge_bound (e:Edge) {δ p:ℝ} (hd:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 rowAt bs kappa (edgeD e) (edgeC e) δ p≤theta-rowFee := by
 have hh := (FinalEdges.closed_envelope_return_cover e hd hp).le
 unfold rowAt
 change Ebase (edgeD e) (edgeC e) δ p+3*edgeD e*(@GenericCount.envelope finalCountScheme kappa δ p)/4≤_
 nlinarith only [hh]

theorem old_rows {d δ p:ℝ} (hd:d∈Set.Icc d0 ds)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 oldExponent bs d δ p≤theta-rowFee := by
 apply old_interval_bound bs hd hδ hp
 · simpa only [oldExponent,oldCapacityAt,edgeD,edgeC,oldCapacity] using edge_bound .oldSmall hδ hp
 · simpa only [oldExponent,oldCapacityAt,edgeD,edgeC,oldCapacity,dm] using edge_bound .oldSwitch hδ hp

theorem new_rows {d δ p:ℝ} (hd:d∈Set.Icc ds dp)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 newExponent bs d δ p≤theta-rowFee := by
 apply new_interval_bound bs hd hδ hp
 · simpa only [newExponent,edgeD,edgeC,dm] using edge_bound .newSwitch hδ hp
 · simpa only [newExponent,edgeD,edgeC] using edge_bound .newTop hδ hp

theorem theta_eq : GenericArithmetic.theta=theta := rfl
theorem y_eq : GenericArithmetic.y=y := rfl
theorem h_eq : GenericArithmetic.h=h := by
 change 1+ell-x=h
 unfold x
 ring
theorem kappa_eq : GenericArithmetic.kappa=kappa := by
 unfold GenericArithmetic.kappa
 rw [theta_eq]
 unfold theta kappa
 ring
theorem dp_eq : GenericArithmetic.dp=dp := by
 change GenericArithmetic.h+1/10000000000=dp
 rw [h_eq]
 rfl

theorem rowAt_eq (bs:List Branch) (κ d C δ p:ℝ) :
 GenericArithmetic.rowAt bs κ d C δ p=rowAt bs κ d C δ p := by
 unfold GenericArithmetic.rowAt rowAt GenericArithmetic.Ebase Ebase
 rw [h_eq]
 rfl
end FinalRows

theorem final_old_rows {d δ p:ℝ}
 (hd:d∈Set.Icc GenericArithmetic.d0 DasStageBFinite.ds)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 GenericArithmetic.rowAt GenericCount.admittedBranches GenericArithmetic.kappa d
  (GenericArithmetic.oldCapacityAt GenericArithmetic.kappa d) δ p≤GenericArithmetic.theta-GenericArithmetic.rowFee := by
 rw [FinalRows.rowAt_eq,FinalRows.theta_eq,FinalRows.kappa_eq]
 change oldExponent FinalRows.bs d δ p≤_
 exact FinalRows.old_rows hd hδ hp

theorem final_new_rows {d δ p:ℝ}
 (hd:d∈Set.Icc DasStageBFinite.ds GenericArithmetic.dp)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 GenericArithmetic.rowAt GenericCount.admittedBranches GenericArithmetic.kappa d
  (min (GenericArithmetic.cap*d)
   ((2*GenericArithmetic.y-(2-DasStageBFinite.physicalB)*d)/DasStageBFinite.physicalLambda)) δ p≤GenericArithmetic.theta-GenericArithmetic.rowFee := by
 rw [FinalRows.rowAt_eq,FinalRows.theta_eq,FinalRows.kappa_eq,FinalRows.y_eq]
 have hd' : d∈Set.Icc DasStageBFinite.ds DasStageBFinite.dp := by simpa only [FinalRows.dp_eq] using hd
 convert FinalRows.new_rows hd' hδ hp using 1 <;> (try simp only [newExponent,DasStageBFinite.newCapacity,GenericArithmetic.cap]) <;> first | rfl | ring
end
end Das.QRH.ReturnB
#print axioms Das.QRH.ReturnB.final_old_rows
#print axioms Das.QRH.ReturnB.final_new_rows
