/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The first common allocation and the second allocation retain separate
prices. Full marked gain is evaluated on the actual surviving widths. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.HighAdmission

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Record12518109Natural.HighAdmission
noncomputable section
open Record12518109Gain

def firstGamma (ν : ℝ) : ℝ := ν-max (3/19) (4*rho ν-5/4)

lemma regular0_eq (T amp S F ν : ℝ) (hd : 5-2*ν≠0) :
    Record12518109Admission.regular T amp S F ν 0 =
      (5-2*ν)*(115-54*ν)*(185-138*ν)*
        (baseMargin T amp ν+(ν-3/19)*S-Record12518109Admission.highFee) := by
  simp only [Record12518109Admission.regular]
  dsimp [Record12518109Admission.d,Record12518109Admission.aa,Record12518109Admission.cc,
    Record12518109Admission.rr,Record12518109Admission.w,baseMargin,rho]
  field_simp [hd]

lemma regular1_eq (T amp S F ν : ℝ) (hd : 5-2*ν≠0) :
    Record12518109Admission.regular T amp S F ν 1 =
      (5-2*ν)*(115-54*ν)*(185-138*ν)*
        (baseMargin T amp ν+(ν-4*rho ν+5/4)*S-Record12518109Admission.highFee) := by
  simp only [Record12518109Admission.regular]
  dsimp [Record12518109Admission.d,Record12518109Admission.aa,Record12518109Admission.cc,
    Record12518109Admission.rr,Record12518109Admission.w,baseMargin,rho]
  field_simp [hd]

/-- The two ordinary common channels pay the weaker actual first-cone rate. -/
theorem regular_common_payment (T amp S F ν : ℝ) (hνhi : ν≤3/4)
    (h0 : 0<Record12518109Admission.regular T amp S F ν 0)
    (h1 : 0<Record12518109Admission.regular T amp S F ν 1) :
    Record12518109Admission.highFee<baseMargin T amp ν+firstGamma ν*S := by
  have hd : 0<5-2*ν := by linarith
  have ha : 0<115-54*ν := by linarith
  have hc : 0<185-138*ν := by linarith
  have hp : 0<(5-2*ν)*(115-54*ν)*(185-138*ν) := by positivity
  rw [regular0_eq T amp S F ν hd.ne'] at h0
  rw [regular1_eq T amp S F ν hd.ne'] at h1
  have hh0 := (mul_pos_iff_of_pos_left hp).mp h0
  have hh1 := (mul_pos_iff_of_pos_left hp).mp h1
  unfold firstGamma
  rcases le_total (3/19:ℝ) (4*rho ν-5/4) with h|h
  · rw [max_eq_right h]
    nlinarith only [hh1]
  · rw [max_eq_left h]
    linarith only [hh0]

lemma firstGamma_bounds {ν : ℝ} (hlo : 31/50≤ν) (hhi : ν≤3/4) :
    1/25≤firstGamma ν ∧ firstGamma ν≤ν := by
  have hd : 0<3*(5-2*ν) := by linarith
  have hh : (137/250:ℝ)≤10*ν/(3*(5-2*ν)) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  have hr : rho ν≤113/250 := by unfold rho;linarith
  have hm : max (3/19:ℝ) (4*rho ν-5/4)≤279/500 := max_le (by norm_num) (by linarith)
  unfold firstGamma
  constructor
  · linarith
  · linarith [le_max_left (3/19:ℝ) (4*rho ν-5/4)]

lemma coeffA_ge_two_coeffC {ν : ℝ} (hlo : 31/50≤ν) (hhi : ν≤3/4) :
    2*coeffC ν≤coeffA ν := by
  have hν : 0≤ν := by linarith
  have hw : 1/2≤5-6*ν := by linarith
  have ha : 0<115-54*ν := by linarith
  have hp := mul_le_mul (show (31/50:ℝ)≤ν from hlo) hw (by norm_num : (0:ℝ)≤1/2) hν
  have hA : (1/20:ℝ)≤coeffA ν := by
    unfold coeffA
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hc := (coefficient_bounds hlo hhi).2.2.2.2.2.2
  linarith

/-- All original slot width is conserved across first removal, second
removal and actual surviving slots. The common-cone cap and the complete
homogeneous gain jointly pay frequency loss without replacing G by a strip. -/
theorem gain_two_allocation_payment
    {ν S F first second live frequency : ℝ}
    (hνlo : 31/50≤ν) (hνhi : ν≤3/4)
    (hfirst : 0≤first) (hsecond : 0≤second) (hlive : 0≤live) (hfreq : 0≤frequency)
    (hwidth : S≤first+second+live) (hfrequency : F-2*(first+second)≤frequency) :
    min (firstGamma ν*S) (gain ν S F) ≤
      firstGamma ν*first+ν*second+gain ν live frequency := by
  obtain ⟨hp,hpν,hA,hAp,hB,hBC,hCsmall⟩ := coefficient_bounds hνlo hνhi
  have hC : 0<coeffC ν := hB.trans hBC
  have hγ := firstGamma_bounds hνlo hνhi
  have hγ0 : 0≤firstGamma ν := by linarith [hγ.1]
  have hγC : 2*coeffC ν≤firstGamma ν := by linarith [hγ.1]
  have hνC : 2*coeffC ν≤ν := hγC.trans hγ.2
  have hA2C := coeffA_ge_two_coeffC hνlo hνhi
  have hAν := hAp.le.trans hpν
  have hcash : firstGamma ν*S≤firstGamma ν*first+ν*second+firstGamma ν*live := by
    have hh := mul_le_mul_of_nonneg_left hwidth hγ0
    have hh' := mul_le_mul_of_nonneg_right hγ.2 hsecond
    nlinarith
  by_cases hcap : firstGamma ν*live≤gain ν live frequency
  · exact (min_le_left _ _).trans (by linarith)
  have hlow : gain ν live frequency<firstGamma ν*live := lt_of_not_ge hcap
  by_cases hphi : phi ν*live≤min (coeffA ν*live+coeffB ν*frequency) (coeffC ν*frequency)
  · have he : gain ν live frequency=phi ν*live := min_eq_left hphi
    have hprice : phi ν≤firstGamma ν := by
      rw [he] at hlow
      have hL : 0<live := by
        by_contra h
        have hz : live=0 := by linarith
        rw [hz] at hlow
        norm_num at hlow
      nlinarith
    have hS := mul_le_mul_of_nonneg_left hwidth hp.le
    have h1 := mul_le_mul_of_nonneg_right hprice hfirst
    have h2 := mul_le_mul_of_nonneg_right hpν hsecond
    exact (min_le_right _ _).trans ((gain_le_phi ν S F).trans (by rw [he];nlinarith))
  have he : gain ν live frequency=min (coeffA ν*live+coeffB ν*frequency) (coeffC ν*frequency) :=
    min_eq_right (le_of_not_ge hphi)
  by_cases hmid : coeffA ν*live+coeffB ν*frequency≤coeffC ν*frequency
  · rw [min_eq_left hmid] at he
    have hf2 : 2*live≤frequency := by
      have hAL := mul_le_mul_of_nonneg_right hA2C hlive
      have hBF := mul_nonneg hB.le hfreq
      nlinarith
    have hBf := mul_le_mul_of_nonneg_left hf2 hB.le
    have hprice : coeffA ν+2*coeffB ν≤firstGamma ν := by
      rw [he] at hlow
      have hL : 0<live := by
        by_contra h
        have hz : live=0 := by linarith
        rw [hz] at hlow
        have := mul_nonneg hB.le hfreq
        nlinarith
      nlinarith
    have hS := mul_le_mul_of_nonneg_left hwidth hA.le
    have hF := mul_le_mul_of_nonneg_left hfrequency hB.le
    have h1 := mul_le_mul_of_nonneg_right hprice hfirst
    have h2 := mul_le_mul_of_nonneg_right (hprice.trans hγ.2) hsecond
    exact (min_le_right _ _).trans ((gain_le_middle ν S F).trans (by rw [he];nlinarith))
  · rw [min_eq_right (le_of_not_ge hmid)] at he
    have hF := mul_le_mul_of_nonneg_left hfrequency hC.le
    have h1 := mul_le_mul_of_nonneg_right hγC hfirst
    have h2 := mul_le_mul_of_nonneg_right hνC hsecond
    exact (min_le_right _ _).trans ((gain_le_C ν S F).trans (by rw [he];nlinarith))

end
end OAI.SevenEighths.Record12518109Natural.HighAdmission
#print axioms OAI.SevenEighths.Record12518109Natural.HighAdmission.regular_common_payment
#print axioms OAI.SevenEighths.Record12518109Natural.HighAdmission.gain_two_allocation_payment
