/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
import Cycle25.Numerator.Scalar.Exponent
import Cycle25.Assembly.Mesh

noncomputable section
namespace Cycle25.Numerator.Scalar
open OAI.SevenEighths.CenteredMomentEnergyWidthRanges
open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

theorem sourceMesh_le {t : ℝ} (ht : 0 < t) : sourceMesh t ≤ t := by
  obtain ⟨_,_,ha,_,_,hm,_,hr,_,_⟩ := bounds 2
    (finalSourceCap 2 0 1 (t/4)) (3/4) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by norm_num) (by positivity)
  change mesh 2 (finalSourceCap 2 0 1 (t/4)) (3/4) (t/4) ≤ t
  linarith

/-- Annular padding uses the actual moment parameter. The common mesh cost
remains explicit until the loss budget is applied. -/
def weightedSourceLoss (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ) : ℝ :=
  3*t+(17/25)*t+
    d*(2*eps+massEps+(3*(159*epsilon+9*t)+momentEps)/4+
      delta*mesh/4+delta*boxWidth/4+q*annulus/(6*kap))+t*ell

theorem weightedSourceLoss_le
    (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ)
    (hk : 7/10 ≤ kap) (_hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/4)
    (hq : 0 ≤ q) (hq1 : q ≤ delta/2)
    (hepsilon : 0 ≤ epsilon) (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (hmesh : 0 ≤ mesh) (hmesh1 : mesh ≤ t)
    (hmass : 0 ≤ massEps) (hmass1 : massEps ≤ t)
    (hmoment : 0 ≤ momentEps) (hmoment1 : momentEps ≤ 2*t)
    (hbox : 0 ≤ boxWidth) (hbox1 : boxWidth ≤ t)
    (hannulus : 0 ≤ annulus) (hannulus1 : annulus ≤ t) :
    weightedSourceLoss kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus ≤
      120*epsilon+2*eps+13*t := by
  have hk0 : 0 < 6*kap := by linarith
  have hdm : delta*mesh ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hmesh1 hdelta).trans
      (mul_le_mul_of_nonneg_right hdelta1 ht)
  have hdb : delta*boxWidth ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hbox1 hdelta).trans
      (mul_le_mul_of_nonneg_right hdelta1 ht)
  have hqt : q*annulus ≤ (3/8)*t :=
    (mul_le_mul_of_nonneg_left hannulus1 hq).trans
      (mul_le_mul_of_nonneg_right (by linarith : q ≤ 3/8) ht)
  have hann : q*annulus/(6*kap) ≤ t/10 := by
    apply (div_le_iff₀ hk0).2
    have hm := mul_le_mul_of_nonneg_right hk ht
    nlinarith
  have hinner : 0 ≤ 2*eps+massEps+(3*(159*epsilon+9*t)+momentEps)/4+
      delta*mesh/4+delta*boxWidth/4+q*annulus/(6*kap) := by positivity
  have hdinner := mul_le_mul_of_nonneg_right hd1 hinner
  have hell : t*ell ≤ t/5 := by
    have hm := mul_le_mul_of_nonneg_left ell_lt_one_fifth.le ht
    linarith
  unfold weightedSourceLoss
  nlinarith only [hdinner,hdm,hdb,hann,hmass1,hmoment1,hepsilon,ht,hell]

theorem weighted_source_packet_exponent
    (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ)
    (hk : kap ≠ 0) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    -ly/2-(4/25)*ell+(3+17/25)*t+t*ell+
      d*(2*eps+massEps+q*(ell/d)-
        q*((2*(ly/d)-1)/(6*kap)-annulus/(3*kap))/2+
        (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
          159*epsilon+9*t)+1+momentEps)/4+
        delta*mesh/4+delta*boxWidth/4-17/50) =
      numeratorExponent kap d delta (q/delta)+
        weightedSourceLoss kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus := by
  unfold numeratorExponent weightedSourceLoss
  have hq : delta*(q/delta)=q := by field_simp
  rw [hq]
  field_simp
  ring

theorem weighted_source_uniform_packet_budget {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) :
    16*D.e+(120*D.ε+2*D.eps+13*D.t)+D.t ≤ (beta-theta)/50 := by
  have hn : 0 ≤ D.eps*(D.N:ℝ) := mul_nonneg D.eps_pos.le (Nat.cast_nonneg _)
  have htell : 0 ≤ D.t*ell := mul_nonneg D.t_pos.le ell_pos.le
  have hb := D.central_budget
  nlinarith only [hb,hn,htell,D.e_pos,D.epsilon_pos,D.eps_pos,D.t_pos]

theorem weighted_source_packet_fixed_budget {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) (d delta q : ℝ)
    (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/4)
    (hq : 0 ≤ q) (hq1 : q ≤ delta/2) :
    16*D.e+weightedSourceLoss D.momentKappa d delta q D.ε D.eps D.t
      (sourceMesh D.t) D.t (2*D.t) D.t D.t+D.t ≤ (beta-theta)/50 := by
  have hl := weightedSourceLoss_le D.momentKappa d delta q D.ε D.eps D.t
    (sourceMesh D.t) D.t (2*D.t) D.t D.t D.momentKappa_lo hd hd1 hdelta hdelta1 hq hq1
    D.epsilon_pos.le D.eps_pos.le D.t_pos.le (sourceMesh_pos D.t_pos).le
    (sourceMesh_le D.t_pos) D.t_pos.le le_rfl (mul_nonneg (by norm_num) D.t_pos.le) le_rfl
    D.t_pos.le le_rfl D.t_pos.le le_rfl
  linarith [weighted_source_uniform_packet_budget D]

/-- The height reserve is retained, while every loss shrinks with beta-theta.
The tighter geometric top is necessary when beta approaches theta. -/
theorem weighted_source_packet_certificate_of_kappa {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) (hbeta : theta < beta)
    (hkap : D.momentKappa = 2*beta-1)
    (d a q : ℝ) (hd : 1/2 ≤ d) (hdtop : d ≤ h+3*D.t)
    (ha : 1/3 ≤ 2*a-1) (ha1 : a ≤ 7/8)
    (hq : 0 ≤ q) (hq1 : q ≤ (2*a-1)/2) :
    numeratorExponent D.momentKappa d (2*a-1) (q/(2*a-1))+
      weightedSourceLoss D.momentKappa d (2*a-1) q D.ε D.eps D.t
        (sourceMesh D.t) D.t (2*D.t) D.t D.t ≤
      signal beta-(beta-theta)/2-weightedSourceSZExponent a D.e-D.t := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdelta1 : 2*a-1 ≤ 3/4 := by linarith
  have hd1 : d ≤ 1 := by linarith [h_interval.2,D.t_small]
  have hp : 0 ≤ q/(2*a-1) ∧ q/(2*a-1) ≤ 1/2 :=
    ⟨div_nonneg hq hdelta.le,(div_le_iff₀ hdelta).2 (by linarith)⟩
  have hb := numerator_supremum_improvement hbeta hd hd1 D.t_pos.le hdtop
    ⟨hdelta.le,hdelta1⟩ hp
  have hbudget := weighted_source_packet_fixed_budget D d (2*a-1) q
    (by linarith) hd1 hdelta.le hdelta1 hq hq1
  rw [←hkap] at hb
  have heq : (1+(2*a-1))/2=a := by ring
  rw [heq] at hb
  have hsz : weightedSourceSZExponent a D.e=weightedSourceSZExponent a 0+16*D.e := by
    unfold weightedSourceSZExponent
    ring
  rw [hsz]
  linarith [D.t_gap]

theorem weighted_source_packet_certificate
    (D : HighParameters.HighData (OAI.SevenEighths.HeckeZeroSupremum.beta-theta))
    (hbeta : theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (d a q : ℝ) (hd : 1/2 ≤ d) (hdtop : d ≤ h+3*D.t)
    (ha : 1/3 ≤ 2*a-1) (ha1 : a ≤ 7/8)
    (hq : 0 ≤ q) (hq1 : q ≤ (2*a-1)/2) :
    numeratorExponent D.momentKappa d (2*a-1) (q/(2*a-1))+
      weightedSourceLoss D.momentKappa d (2*a-1) q D.ε D.eps D.t
        (sourceMesh D.t) D.t (2*D.t) D.t D.t ≤
      signal OAI.SevenEighths.HeckeZeroSupremum.beta-
        (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2-
        weightedSourceSZExponent a D.e-D.t := by
  exact weighted_source_packet_certificate_of_kappa D hbeta D.momentKappa_exact
    d a q hd hdtop ha ha1 hq hq1

end Cycle25.Numerator.Scalar
