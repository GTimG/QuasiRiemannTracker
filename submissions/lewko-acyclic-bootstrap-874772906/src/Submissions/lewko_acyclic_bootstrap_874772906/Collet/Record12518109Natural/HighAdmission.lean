/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The rational channels are exactly Record12518109Admission.Formulas.regular;
the gain is the checked homogeneous gain, with no historical source-plane
or amplifier constants inserted into the payment. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Admission.Formulas
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Homogeneous

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Natural.HighAdmission
noncomputable section
open Record12518109Gain

/-- The unsplit physical HIGH margin, before marked gain. -/
def baseMargin (T amp ν : ℝ) : ℝ :=
  1-ν*T-5*amp-rho ν*(1-6*amp)

lemma regular2_eq (T amp S F ν : ℝ) (hd : 5-2*ν≠0) :
    Record12518109Admission.regular T amp S F ν 2 =
      (5-2*ν)*(115-54*ν)*(185-138*ν)*
        (baseMargin T amp ν+phi ν*S-Record12518109Admission.highFee) := by
  simp only [Record12518109Admission.regular]
  dsimp [Record12518109Admission.d,Record12518109Admission.aa,Record12518109Admission.cc,
    Record12518109Admission.rr,Record12518109Admission.w,baseMargin,rho,phi]
  field_simp [hd]

lemma regular3_eq (T amp S F ν : ℝ) (hd : 5-2*ν≠0) (ha : 115-54*ν≠0) :
    Record12518109Admission.regular T amp S F ν 3 =
      (5-2*ν)*(115-54*ν)*(185-138*ν)*
        (baseMargin T amp ν+coeffA ν*S+coeffB ν*F-Record12518109Admission.highFee) := by
  simp only [Record12518109Admission.regular]
  dsimp [Record12518109Admission.d,Record12518109Admission.aa,Record12518109Admission.cc,
    Record12518109Admission.rr,Record12518109Admission.w,baseMargin,rho,coeffA,coeffB]
  simp only [mul_comm (54:ℝ) ν] at *
  field_simp [hd, ha]
  <;> ring

lemma regular4_eq (T amp S F ν : ℝ) (hd : 5-2*ν≠0) (hc : 185-138*ν≠0) :
    Record12518109Admission.regular T amp S F ν 4 =
      (5-2*ν)*(115-54*ν)*(185-138*ν)*
        (baseMargin T amp ν+coeffC ν*F-Record12518109Admission.highFee) := by
  simp only [Record12518109Admission.regular]
  dsimp [Record12518109Admission.d,Record12518109Admission.aa,Record12518109Admission.cc,
    Record12518109Admission.rr,Record12518109Admission.w,baseMargin,rho,coeffC]
  simp only [mul_comm (138:ℝ) ν] at *
  field_simp [hd, hc]
  <;> ring

/-- The three cleared homogeneous HIGH channels imply precisely the full
G payment used by the actual root supplier. -/
theorem regular_gain_payment (T amp S F ν : ℝ)
    (hνlo : 31/50≤ν) (hνhi : ν≤3/4)
    (h2 : 0<Record12518109Admission.regular T amp S F ν 2)
    (h3 : 0<Record12518109Admission.regular T amp S F ν 3)
    (h4 : 0<Record12518109Admission.regular T amp S F ν 4) :
    ν*T+5*amp+rho ν*(1-6*amp)-gain ν S F < 1-Record12518109Admission.highFee := by
  have hd : 0<5-2*ν := by linarith
  have ha : 0<115-54*ν := by linarith
  have hc : 0<185-138*ν := by linarith
  have hp : 0<(5-2*ν)*(115-54*ν)*(185-138*ν) := by positivity
  rw [regular2_eq T amp S F ν hd.ne'] at h2
  rw [regular3_eq T amp S F ν hd.ne' ha.ne'] at h3
  rw [regular4_eq T amp S F ν hd.ne' hc.ne'] at h4
  have hphi := (mul_pos_iff_of_pos_left hp).mp h2
  have hmid := (mul_pos_iff_of_pos_left hp).mp h3
  have hlast := (mul_pos_iff_of_pos_left hp).mp h4
  have hg : Record12518109Admission.highFee-baseMargin T amp ν < gain ν S F :=
    lt_min (by linarith) (lt_min (by linarith) (by linarith))
  dsimp only [baseMargin] at hg
  linarith

/-- Explicit admission, scaling and two-allocation loss for the physical
HIGH exponent. Only scalar source geometry and the full root gain enter. -/
theorem scaled_gain_payment
    (ν D T amp S F removed live frequency fee target exponent gamma : ℝ)
    (hνlo : 31/50≤ν) (hνhi : ν≤3/4) (hD : 0≤D) (hr : 0≤removed)
    (hS : D*S≤live) (hF : D*F-2*removed≤frequency)
    (hgamma : 2*coeffC ν≤gamma)
    (hadmit : fee≤baseMargin T amp ν+gain ν S F)
    (hsource : exponent≤target-D*baseMargin T amp ν-gamma*removed) :
    exponent-gain ν live frequency≤target-D*fee := by
  have hbase := gain_width_loss (S:=D*S) (F:=D*F) (q:=D*F-2*removed)
    hνlo hνhi (by linarith)
  have hmono := gain_mono hνlo hνhi hS hF
  rw [gain_homogeneous ν S F D hD] at hbase
  have hscale := mul_le_mul_of_nonneg_left hadmit hD
  have hremove := mul_le_mul_of_nonneg_right hgamma hr
  nlinarith

end
end OAI.SevenEighths.Record12518109Natural.HighAdmission
#print axioms OAI.SevenEighths.Record12518109Natural.HighAdmission.regular_gain_payment
#print axioms OAI.SevenEighths.Record12518109Natural.HighAdmission.scaled_gain_payment
