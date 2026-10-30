/- Repeated marks: fork of Collet's final-stage module FinalRows (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): old rows on `[d0, 19/25]`, new rows on `[19/25, dp]` with the physical
cap `numeratorCap = 3/50`; the certificate reserve `1/10^8` is weakened to the generic `rowFee = 1/10^9`. -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return; the reserve literal of `FinalRows.reserve_le` follows Constants.lean (no other change). -/
/- Modified by ArviFoxy (2026-10-29): forked into Submissions.arvi_return_tuning, namespace QRH.ArviDensity.Return.Tuning, over the reflective windows and edge covers of this package (`w.toAdmitted` written as `ReturnCountWindow.toAdmitted w`). -/
import Submissions.arvi_selected_leaf.Tuning.EdgeCertificates
import Submissions.arvi_selected_leaf.Return.Conductor
import Submissions.arvi_density.ReturnD.Schedule
import Submissions.arvi_selected_leaf.Return.TransportInstances
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.ArviDensity.Return.Tuning
open QRH.Record1252270103Return QRH.ArviReturnTuning
noncomputable section
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Geometry.BoundsN := Geometry.finalBounds
local instance : CountScheme := finalCountScheme
namespace FinalRows

abbrev bs : List Branch := GenericCount.admittedBranches

theorem edge_bound (e:Edge) {δ p:ℝ} (hd:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 rowAt bs kappa (edgeD e) (edgeC e) δ p≤theta-reserve := by
 have hh := (FinalEdges.closed_envelope_return_cover e hd hp).le
 unfold rowAt
 change Ebase (edgeD e) (edgeC e) δ p+3*edgeD e*(@GenericCount.envelope finalCountScheme kappa δ p)/4≤_
 nlinarith only [hh]

theorem old_rows {d δ p:ℝ} (hd:d∈Set.Icc d0 dm)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 oldExponent bs d δ p≤theta-reserve := by
 apply old_interval_bound bs hd hδ hp
 · simpa only [oldExponent,oldCapacityAt,edgeD,edgeC,oldCapacity] using edge_bound .oldSmall hδ hp
 · simpa only [oldExponent,oldCapacityAt,edgeD,edgeC,oldCapacity] using edge_bound .oldSwitch hδ hp

theorem new_rows {d δ p:ℝ} (hd:d∈Set.Icc dm dp)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 newExponent bs d δ p≤theta-reserve := by
 apply new_interval_bound bs hd hδ hp
 · simpa only [newExponent,edgeD,edgeC] using edge_bound .newSwitch hδ hp
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

theorem reserve_le : theta-reserve≤GenericArithmetic.theta-GenericArithmetic.rowFee := by
 rw [theta_eq]
 have h1 : GenericArithmetic.rowFee = (1/1000000000:ℝ) := rfl
 have h2 : reserve = (1/100000000:ℝ) := rfl
 rw [h1,h2]
 linarith
end FinalRows

theorem final_old_rows {d δ p:ℝ}
 (hd:d∈Set.Icc GenericArithmetic.d0 QRH.ArviDensity.Return.dm)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 GenericArithmetic.rowAt GenericCount.admittedBranches GenericArithmetic.kappa d
  (GenericArithmetic.oldCapacityAt GenericArithmetic.kappa d) δ p≤GenericArithmetic.theta-GenericArithmetic.rowFee := by
 refine le_trans ?_ FinalRows.reserve_le
 rw [FinalRows.rowAt_eq,FinalRows.kappa_eq]
 change oldExponent FinalRows.bs d δ p≤_
 exact FinalRows.old_rows hd hδ hp

theorem final_new_rows {d δ p:ℝ}
 (hd:d∈Set.Icc QRH.ArviDensity.Return.dm GenericArithmetic.dp)
 (hδ:δ∈Set.Icc 0 (3/4)) (hp:p∈Set.Icc 0 (1/2)) :
 GenericArithmetic.rowAt GenericCount.admittedBranches GenericArithmetic.kappa d
  (min (QRH.ArviDensity.Return.numeratorCap*d)
   ((2*GenericArithmetic.y-(2-QRH.ArviDensity.Return.physicalB)*d)/QRH.ArviDensity.Return.physicalLambda)) δ p≤GenericArithmetic.theta-GenericArithmetic.rowFee := by
 refine le_trans ?_ FinalRows.reserve_le
 rw [FinalRows.rowAt_eq,FinalRows.kappa_eq,FinalRows.y_eq]
 have hd' : d∈Set.Icc QRH.ArviDensity.Return.dm QRH.ArviDensity.Return.dp := by simpa only [FinalRows.dp_eq] using hd
 exact FinalRows.new_rows hd' hδ hp
end
end QRH.ArviDensity.Return.Tuning
