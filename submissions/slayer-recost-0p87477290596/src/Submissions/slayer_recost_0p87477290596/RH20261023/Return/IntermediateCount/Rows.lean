/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact finite envelope rows instantiated in the generic physical geometry. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.IntermediateCount.EdgeCertificates
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.IntermediateCount.Conductor
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.TransportInstances
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RH20261023Return.IntermediateCount
noncomputable section
local instance : Geometry.Parameters := Geometry.intermediateParameters
local instance : Geometry.Bounds := Geometry.intermediateBounds
local instance : CountScheme := countScheme
namespace ConcreteRows
open RH20261023Return.C30
abbrev bs : List Branch := GenericCount.admittedBranches

theorem edge_bound (e:Edge) {δ p:ℝ} (hd:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 rowAt bs kappa (edgeD e) (edgeC e) δ p≤theta-rowFee := by
 have hh := (Edges.closed_envelope_return_cover e hd hp).le
 unfold rowAt
 change Ebase (edgeD e) (edgeC e) δ p+3*edgeD e*(@GenericCount.envelope countScheme kappa δ p)/4≤_
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

theorem theta_eq : GenericArithmetic.theta=theta := by
 change (8747759/10000000:ℝ)=theta
 norm_num [theta,c]
theorem y_eq : GenericArithmetic.y=y := by
 change (6969163/15000000:ℝ)=y
 norm_num [y,h,ell,c]
theorem ell_eq : GenericArithmetic.ell=ell := by
 change (1256723/7500000:ℝ)=ell
 norm_num [ell,c]
theorem h_eq : GenericArithmetic.h=h := by
 change 1+(1256723/7500000:ℝ)-5517391/15000000=h
 norm_num [h]
theorem kappa_eq : GenericArithmetic.kappa=kappa := by
 unfold GenericArithmetic.kappa
 rw [theta_eq]
 norm_num [theta,kappa,c]
theorem dp_eq : GenericArithmetic.dp=dp := by
 change GenericArithmetic.h+1/10000000000=dp
 rw [h_eq]
 norm_num [dp,h]

theorem rowAt_eq (bs:List Branch) (κ d C δ p:ℝ) :
 GenericArithmetic.rowAt bs κ d C δ p=rowAt bs κ d C δ p := by
 unfold GenericArithmetic.rowAt rowAt GenericArithmetic.Ebase Ebase
 rw [h_eq,y_eq,ell_eq]
end ConcreteRows

theorem old_rows {d δ p:ℝ}
 (hd:d∈Set.Icc GenericArithmetic.d0 RH20261023Return.C30.ds)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 GenericArithmetic.rowAt GenericCount.admittedBranches GenericArithmetic.kappa d
  (GenericArithmetic.oldCapacityAt GenericArithmetic.kappa d) δ p≤GenericArithmetic.theta-GenericArithmetic.rowFee := by
 rw [ConcreteRows.rowAt_eq,ConcreteRows.theta_eq,ConcreteRows.kappa_eq]
 unfold GenericArithmetic.oldCapacityAt
 rw [ConcreteRows.y_eq]
 change oldExponent ConcreteRows.bs d δ p≤_
 exact ConcreteRows.old_rows hd hδ hp

theorem new_rows {d δ p:ℝ}
 (hd:d∈Set.Icc RH20261023Return.C30.ds GenericArithmetic.dp)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 GenericArithmetic.rowAt GenericCount.admittedBranches GenericArithmetic.kappa d
  (min (GenericArithmetic.cap*d)
   ((2*GenericArithmetic.y-(2-RH20261023Return.C30.physicalB)*d)/RH20261023Return.C30.physicalLambda)) δ p≤GenericArithmetic.theta-GenericArithmetic.rowFee := by
 rw [ConcreteRows.rowAt_eq,ConcreteRows.theta_eq,ConcreteRows.kappa_eq,ConcreteRows.y_eq]
 have hd' : d∈Set.Icc RH20261023Return.C30.ds RH20261023Return.C30.dp := by simpa only [ConcreteRows.dp_eq] using hd
 convert ConcreteRows.new_rows hd' hδ hp using 1 <;> (try simp only [newExponent,RH20261023Return.C30.newCapacity,GenericArithmetic.cap]) <;> first | rfl | ring
end
end QRH.RH20261023Return.IntermediateCount
#print axioms QRH.RH20261023Return.IntermediateCount.old_rows
#print axioms QRH.RH20261023Return.IntermediateCount.new_rows
