/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Lower-conductor feedback with arbitrary positive row fee. Adapted from PR137
GenericFeedback/SourceLedger (Sil and predecessor authors, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSchedule

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Scalar
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return.GenericPhysical
open OAI.SevenEighths
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]
variable [S : Schedule (line := line)]
include S

def oldExponent (bs : List Branch) (d delta p : ℝ) : ℝ :=
  rowAt bs kappa d (oldCapacityAt kappa d) delta p
def oldExponentAt (bs : List Branch) (K d delta p : ℝ) : ℝ :=
  rowAt bs K d (oldCapacityAt K d) delta p

theorem old_feedback (bs : List Branch) {κ d δ p : ℝ} (hk : kappa ≤ κ)
    (hd : d ∈ Set.Icc 0 dm) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt bs κ d δ p-oldExponent bs d δ p ≤ (κ-kappa)/8 := by
  have ha : (7/10:ℝ) ≤ kappa := by dsimp [kappa]; linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.theta_bounds.1]
  have hk7 := ha.trans hk
  have ha0 : 0 < kappa := by linarith
  have hk0 : 0 < κ := by linarith
  have hg : 0 ≤ κ-kappa := sub_nonneg.mpr hk
  have hc := QRH.Record12518109Return.envelope_gap bs ha hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1,hδ.2]) hp
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hd1 : d ≤ 1 := by exact hd.2.trans (show dm ≤ (1:ℝ) by norm_num [dm])
  have hdp := mul_le_mul_of_nonneg_right hd1 hg
  have hprod : (7/10:ℝ)^2 ≤ κ*kappa := by
    rw [pow_two]
    exact mul_le_mul hk7 ha (by norm_num) hk0.le
  have hinvid : 1/kappa-1/κ=(κ-kappa)/(κ*kappa) := by field_simp
  have hinv : 1/kappa-1/κ ≤ (κ-kappa)/((7/10:ℝ)^2) := by
    rw [hinvid]
    exact div_le_div_of_nonneg_left hg (by norm_num) hprod
  have hmin0 : 0 ≤ min d (2*y-d) := by
    apply le_min hd.1
    have hh := S.switch_before_twoy
    have hdm : d ≤ (19/25:ℝ) := hd.2
    linarith
  have hmin := min_capacity_upper d
  have hδp : δ*p ≤ 3/8 := by
    have := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    linarith
  have hcoef0 : 0 ≤ δ*p*min d (2*y-d)/12 :=
    div_nonneg (mul_nonneg (mul_nonneg hδ.1 hp.1) hmin0) (by norm_num)
  have hcoef : δ*p*min d (2*y-d)/12 ≤ 1/64 := by
    have := mul_le_mul hδp hmin hmin0 (by norm_num : (0:ℝ) ≤ 3/8)
    linarith
  have hi : (δ*p*min d (2*y-d)/12)*(1/kappa-1/κ) ≤
      (1/64)*((κ-kappa)/((7/10:ℝ)^2)) := by
    calc
      _ ≤ (δ*p*min d (2*y-d)/12)*((κ-kappa)/((7/10:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hinv hcoef0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have he : oldExponentAt bs κ d δ p-oldExponent bs d δ p =
      (3*d/4)*(envelope bs κ δ p-envelope bs kappa δ p)+
      (δ*p*min d (2*y-d)/12)*(1/kappa-1/κ) := by
    unfold oldExponentAt oldExponent rowAt Ebase oldCapacityAt
    field_simp
    ring
  rw [he]
  ring_nf at hm hdp hi ⊢
  linarith only [hm,hdp,hi,hg]


theorem old_packet_certificate (bs : List Branch) {beta d delta p e height : ℝ} (L : LossData)
    (hbeta : theta < beta) (_hupper : beta ≤ 7/8)
    (hd : d ∈ Set.Icc d0 dm) (hdelta : delta ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2))
    (hbase : oldExponent bs d delta p ≤ theta-rowFee)
    (hbudget : 16*e+weightedSourceLoss d delta L+height ≤ (beta-theta)/4) :
    numeratorExponent bs (2*beta-1) d (oldCapacityAt (2*beta-1) d) delta p+
      kernelExponent ((1+delta)/2) e+weightedSourceLoss d delta L <
      beta+Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift-
        sourceReserve-(beta-theta)/2-height := by
  have hd' : d ∈ Set.Icc (0:ℝ) dm := ⟨(show (0:ℝ) ≤ d0 by norm_num [d0]).trans hd.1,hd.2⟩
  have hk : kappa ≤ 2*beta-1 := by unfold kappa; linarith
  have hf := old_feedback bs hk hd' hdelta hp
  have hi := numerator_kernel_exponent bs (2*beta-1) d (oldCapacityAt (2*beta-1) d) delta p e
  dsimp only [oldExponentAt,oldExponent] at hf hbase
  unfold kappa at hf hbase
  unfold sourceReserve rowFee at *
  linarith [S.fee_pos]

lemma old_physical_packet_certificate (D : QRH.Record1252270103Return.GenericPhysical.BaselineData) (eps sigma d a q : ℝ)
    (hgap : theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hbeta : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ 7/8)
    (hk : D.momentKappa=2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+8*D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
    (hd : d0 ≤ d ∧ d ≤ dm) (ha : 51/100 ≤ a) (hatop : a ≤ 7/8)
    (hq : 0 ≤ q ∧ q ≤ (2*a-1)/2) :
    numeratorExponent Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.admittedBranches D.momentKappa d (oldCapacityAt D.momentKappa d) (2*a-1) (q/(2*a-1))+
      weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma 0) ≤
      Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signal OAI.SevenEighths.HeckeZeroSupremum.beta-sourceReserve-
        (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdel : 0 ≤ 2*a-1 ∧ 2*a-1 ≤ 3/4 := by constructor <;> linarith
  have hp : q/(2*a-1) ∈ Set.Icc 0 (1/2) :=
    ⟨div_nonneg hq.1 hdelta.le,(div_le_iff₀ hdelta).mpr (by linarith [hq.2])⟩
  have hd1 : d ≤ 1 := hd.2.trans (by norm_num [dm])
  have hl := physical_loss_bound D eps sigma 0 d (2*a-1) heps hsigma (by norm_num) hd1 hdel
  have hh := old_packet_certificate Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.admittedBranches (physicalLoss D eps sigma 0) hgap hbeta hd hdel hp (S.old_rows hd hdel hp)
    (by linarith : 16*D.e+weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma 0)+D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
  rw [←hk,show (1+(2*a-1))/2=a by ring] at hh
  dsimp only [Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signal,
    Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signal]
  linarith
end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
