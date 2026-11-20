/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.PacketJoinAbsorbed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The existing source mesh is chosen before the live cells. This is the
original schedule inequality, with no historical geometry instance. -/
lemma native_sourceMesh_le {t : ℝ} (ht : 0 < t) : Cycle25.sourceMesh t ≤ t := by
  obtain ⟨_,_,ha,_,_,hm,_,hr,_,_⟩ :=
    CenteredMomentEnergyWidthSchedule.bounds 2
      (CenteredMomentEnergyWidthRanges.finalSourceCap 2 0 1 (t/4)) (3/4) (t/4)
      (by norm_num) (CenteredMomentEnergyWidthRanges.sourceCap_nonneg 2 0 1
        (by norm_num) (by norm_num) _) (by norm_num) (by positivity)
  change CenteredMomentEnergyWidthSchedule.mesh 2
    (CenteredMomentEnergyWidthRanges.finalSourceCap 2 0 1 (t/4)) (3/4) (t/4) ≤ t
  linarith

lemma native_mass_cost_le (D : BaselineData) (a d : ℝ)
    (hd : 0 < d) (hd' : d ≤ 1) (ha : 1/2 ≤ a) (ha' : a ≤ 7/8) :
    d*nativeMass D a d ≤ 3*D.t := by
  have hDt := D.t_pos
  have hmesh := native_sourceMesh_le D.t_pos
  have hm0 := (Cycle25.sourceMesh_pos D.t_pos).le
  have hδ : 0 ≤ 2*a-1 := by linarith
  have hδ' : 2*a-1 ≤ 3/4 := by linarith
  have hm : (2*a-1)*Cycle25.sourceMesh D.t/4 ≤ 3*D.t/16 := by
    nlinarith [mul_le_mul hδ' hmesh hm0 (by norm_num : (0:ℝ) ≤ 3/4)]
  have ht : (2*a-1)*D.t ≤ 3*D.t/4 := by nlinarith [D.t_pos]
  have hell := Geometry.ell_lt_fifth
  have hexpand : d*nativeMass D a d =
      d*(D.t+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*D.t)+D.t*Geometry.ell := by
    unfold nativeMass
    field_simp
    <;> ring
  rw [hexpand]
  have hbase : 0 ≤ D.t+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*D.t := by positivity
  have hprod := mul_le_mul_of_nonneg_right hd' hbase
  nlinarith [mul_le_mul_of_nonneg_left hell.le D.t_pos.le]

/-- A scalar reserve fixed before Z pays every native count, source, contour
and logarithm charge, for the exact FinalPowerCells integration fee. -/
lemma native_early_budget (D : BaselineData) (P : TransportParameters D)
    (a d eps affineError loss : ℝ) (hd : 0 < d) (hd' : d ≤ 1)
    (ha : 1/2 ≤ a) (ha' : a ≤ 7/8) (heps : 0 ≤ eps)
    (haff : 0 ≤ affineError) (hloss : 0 ≤ loss) (hm : 0 ≤ P.mesh)
    (hreserve : 159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+affineError/4+loss ≤ 1/5000000) :
    d*(3*(159*D.ε+8*D.t+P.mesh)/4+nativeMoment D affineError/4+nativeMass D a d)+
      (16*D.e+2*eps*d+17*D.t/25)+d*loss ≤ 1/5000000 := by
  have hDt := D.t_pos
  have hDep := D.epsilon_pos
  have hmass := native_mass_cost_le D a d hd hd' ha ha'
  have hcount := mul_le_mul_of_nonneg_right hd'
    (show 0 ≤ 3*(159*D.ε+8*D.t+P.mesh)/4 by positivity)
  have hmoment := mul_le_mul_of_nonneg_right hd'
    (show 0 ≤ nativeMoment D affineError/4 by unfold nativeMoment;positivity)
  have he := mul_le_mul_of_nonneg_left hd' heps
  have hl := mul_le_mul_of_nonneg_right hd' hloss
  unfold nativeMoment at hmoment ⊢
  nlinarith [D.epsilon_pos,D.t_pos]

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.native_early_budget
