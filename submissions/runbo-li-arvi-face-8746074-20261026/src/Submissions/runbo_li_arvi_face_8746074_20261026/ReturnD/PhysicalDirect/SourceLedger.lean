/- Repeated marks: fork of Collet's generic return module PhysicalDirect.SourceLedger (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Literal physical source loss ledger at the new GenericCount.envelope. Apache-2.0.
Adapted from Gao Target830 with the checked new conductor/feedback certificates. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Schedule
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.GenericScalar
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.PhysicalDirect.Data
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.GenericScalar
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Mesh
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic QRH.Record12518109Count QRH.RepeatedMarks.Return.GenericPhysical.Scalar
open QRH.Record12518109Count
open QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect QRH.Record1252270103Return.GenericPhysical
open QRH.RepeatedMarks.Return.GenericArithmetic

def physicalLoss (D : BaselineData) (eps sigma affineError : ℝ) : LossData where
  front := 3*D.t
  frequency := (17/25)*D.t
  scalar := 2*eps
  mass := D.t
  count := sigma
  moment := D.t+affineError+D.t
  selection := 0
  mesh := Cycle25.sourceMesh D.t+4*D.t
  slack := D.t

lemma sourceMesh_le {t : ℝ} (ht : 0< t) : Cycle25.sourceMesh t ≤ t := by
  obtain ⟨_,_,ha,_,_,hm,_,hr,_,_⟩ :=
    OAI.SevenEighths.CenteredMomentEnergyWidthSchedule.bounds 2
      (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.finalSourceCap 2 0 1 (t/4))
      (3/4) (t/4) (by norm_num)
      (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
      (by norm_num) (by positivity)
  change OAI.SevenEighths.CenteredMomentEnergyWidthSchedule.mesh 2
    (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.finalSourceCap 2 0 1 (t/4)) (3/4) (t/4) ≤ t
  linarith

lemma physical_loss_bound (D : BaselineData) (eps sigma affineError d delta : ℝ)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma) (haff : 0 ≤ affineError)
    (hd : d ≤ 1) (hdelta : 0 ≤ delta ∧ delta ≤ 3/4) :
    weightedSourceLoss d delta (physicalLoss D eps sigma affineError) ≤
      2*eps+3*sigma/4+affineError/4+7*D.t := by
  have hm := (Cycle25.sourceMesh_pos D.t_pos).le
  have ht := D.t_pos.le
  have hl := weightedSourceLoss_le_uniform (physicalLoss D eps sigma affineError) hd hdelta
    (by dsimp [physicalLoss];positivity) ht hsigma (by dsimp [physicalLoss];positivity)
    (by simp [physicalLoss]) (by dsimp [physicalLoss];positivity)
  have hmesh := sourceMesh_le D.t_pos
  have hell : ell ≤ (1/5:ℝ) := by linarith [Geometry.ell_pos,Geometry.ell_lt_fifth]
  have hte := mul_le_mul_of_nonneg_left hell ht
  dsimp [uniformSourceLoss,physicalLoss] at hl
  dsimp only [physicalLoss]
  linarith

lemma physical_packet_certificate (D : BaselineData) (eps sigma affineError d a q : ℝ)
    (hgap : theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hbeta : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ 7/8)
    (hk : D.momentKappa=2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma) (haff : 0 ≤ affineError)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
    (hd : dm ≤ d ∧ d ≤ dp) (ha : 51/100 ≤ a) (hatop : a ≤ 7/8)
    (hq : 0 ≤ q ∧ q ≤ (2*a-1)/2) :
    numeratorExponent GenericCount.admittedBranches D.momentKappa d (newCapacity d) (2*a-1) (q/(2*a-1))+
      weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError) ≤
      Assembly.signal OAI.SevenEighths.HeckeZeroSupremum.beta-sourceReserve-
        (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdel : 0 ≤ 2*a-1 ∧ 2*a-1 ≤ 3/4 := by constructor <;> linarith
  have hp : q/(2*a-1) ∈ Set.Icc 0 (1/2) :=
    ⟨div_nonneg hq.1 hdelta.le,(div_le_iff₀ hdelta).mpr (by linarith [hq.2])⟩
  have hd1 : d ≤ 1 := hd.2.trans (by change Geometry.h+1/10000000000 ≤ _; linarith [Geometry.BoundsR.h_interval.2])
  have hl := physical_loss_bound D eps sigma affineError d (2*a-1) heps hsigma haff hd1 hdel
  have hh := new_packet_certificate GenericCount.admittedBranches (physicalLoss D eps sigma affineError) hgap hbeta hd hdel hp (PhysicalSchedule.new_rows hd hdel hp)
    (by linarith : 16*D.e+weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError)+D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
  rw [←hk,show (1+(2*a-1))/2=a by ring] at hh
  linarith
lemma old_physical_packet_certificate (D : BaselineData) (eps sigma d a q : ℝ)
    (hgap : theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hbeta : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ 7/8)
    (hk : D.momentKappa=2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+8*D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
    (hd : d0 ≤ d ∧ d ≤ dm) (ha : 51/100 ≤ a) (hatop : a ≤ 7/8)
    (hq : 0 ≤ q ∧ q ≤ (2*a-1)/2) :
    numeratorExponent GenericCount.admittedBranches D.momentKappa d (oldCapacityAt D.momentKappa d) (2*a-1) (q/(2*a-1))+
      weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma 0) ≤
      Assembly.signal OAI.SevenEighths.HeckeZeroSupremum.beta-sourceReserve-
        (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdel : 0 ≤ 2*a-1 ∧ 2*a-1 ≤ 3/4 := by constructor <;> linarith
  have hp : q/(2*a-1) ∈ Set.Icc 0 (1/2) :=
    ⟨div_nonneg hq.1 hdelta.le,(div_le_iff₀ hdelta).mpr (by linarith [hq.2])⟩
  have hd1 : d ≤ 1 := hd.2.trans (PhysicalSchedule.dMinus_before_top.trans RepeatedMarksReturn.Transport.Arithmetic.dPlus_lt_one.le)
  have hl := physical_loss_bound D eps sigma 0 d (2*a-1) heps hsigma (by norm_num) hd1 hdel
  have hh := old_packet_certificate GenericCount.admittedBranches (physicalLoss D eps sigma 0) hgap hbeta hd hdel hp (PhysicalSchedule.old_rows hd hdel hp)
    (by linarith : 16*D.e+weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma 0)+D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
  rw [←hk,show (1+(2*a-1))/2=a by ring] at hh
  linarith
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.Source
