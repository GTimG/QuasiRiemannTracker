import Candidate.Uneven.BootstrapCore
import Candidate.Uneven.SaturatedGain

/- Original module: Candidate.Uneven.BootstrapSmallWidth. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem small_slope_1 {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ Saturated.slope d 0-Saturated.slope d 1 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-200*(d^2))+(96*(d^3))+(100*d)) := by
    have he : ((-200*(d^2))+(96*(d^3))+(100*d))=124992*(d-31/50)^0*(33/50-d)^3+351668*(d-31/50)^1*(33/50-d)^2+327824*(d-31/50)^2*(33/50-d)^1+101244*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (125+(-140*d)+(36*(d^2))) := by
    have he : (125+(-140*d)+(36*(d^2)))=(30176/625:ℝ)+2348*(d-31/50)^0*(33/50-d)^2+2312*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have he : Saturated.slope d 0-Saturated.slope d 1=((-200*(d^2))+(96*(d^3))+(100*d))/(125+(-140*d)+(36*(d^2))) := by
    norm_num [Saturated.slope,Saturated.offset,auxLower]
    field_simp (disch := first | positivity | linarith) <;> ring
  rw [he]
  exact div_nonneg hn hden.le

theorem small_cap_1 {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ Saturated.offset d 1+auxLower*(Saturated.slope d 1-Saturated.slope d 0) := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-13200*(d^2))+(5350*d)+(8136*(d^3))) := by
    have he : ((-13200*(d^2))+(5350*d)+(8136*(d^3)))=2843072*(d-31/50)^0*(33/50-d)^3+7506988*(d-31/50)^1*(33/50-d)^2+6533084*(d-31/50)^2*(33/50-d)^1+1877304*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (46875+(-52500*d)+(13500*(d^2))) := by
    have he : (46875+(-52500*d)+(13500*(d^2)))=(90528/5:ℝ)+880500*(d-31/50)^0*(33/50-d)^2+867000*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have he : Saturated.offset d 1+auxLower*(Saturated.slope d 1-Saturated.slope d 0)=((-13200*(d^2))+(5350*d)+(8136*(d^3)))/(46875+(-52500*d)+(13500*(d^2))) := by
    norm_num [Saturated.slope,Saturated.offset,auxLower]
    field_simp (disch := first | positivity | linarith) <;> ring
  rw [he]
  exact div_nonneg hn hden.le

theorem small_slope_2 {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ Saturated.slope d 0-Saturated.slope d 2 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-400*(d^2))+(156*(d^3))+(225*d)) := by
    have he : ((-400*(d^2))+(156*(d^3))+(225*d))=358112*(d-31/50)^0*(33/50-d)^3+1017398*(d-31/50)^1*(33/50-d)^2+957714*(d-31/50)^2*(33/50-d)^1+298584*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (575+(-500*d)+(108*(d^2))) := by
    have he : (575+(-500*d)+(108*(d^2)))=(182528/625:ℝ)+9044*(d-31/50)^0*(33/50-d)^2+8936*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have he : Saturated.slope d 0-Saturated.slope d 2=((-400*(d^2))+(156*(d^3))+(225*d))/(575+(-500*d)+(108*(d^2))) := by
    norm_num [Saturated.slope,Saturated.offset,auxLower]
    field_simp (disch := first | positivity | linarith) <;> ring
  rw [he]
  exact div_nonneg hn hden.le

theorem small_cap_2 {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ Saturated.offset d 2+auxLower*(Saturated.slope d 2-Saturated.slope d 0) := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-11400*(d^2))+(4225*d)+(7596*(d^3))) := by
    have he : ((-11400*(d^2))+(4225*d)+(7596*(d^3)))=744992*(d-31/50)^0*(33/50-d)^3+1515418*(d-31/50)^1*(33/50-d)^2+864074*(d-31/50)^2*(33/50-d)^1+101244*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (215625+(-187500*d)+(40500*(d^2))) := by
    have he : (215625+(-187500*d)+(40500*(d^2)))=(547584/5:ℝ)+3391500*(d-31/50)^0*(33/50-d)^2+3351000*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have he : Saturated.offset d 2+auxLower*(Saturated.slope d 2-Saturated.slope d 0)=((-11400*(d^2))+(4225*d)+(7596*(d^3)))/(215625+(-187500*d)+(40500*(d^2))) := by
    norm_num [Saturated.slope,Saturated.offset,auxLower]
    field_simp (disch := first | positivity | linarith) <;> ring
  rw [he]
  exact div_nonneg hn hden.le

theorem small_slope_3 {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ Saturated.slope d 0-Saturated.slope d 3 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-6*(d^2))+(5*d)) := by
    have he : ((-6*(d^2))+(5*d))=496*(d-31/50)^0*(33/50-d)^2+931*(d-31/50)^1*(33/50-d)^1+429*(d-31/50)^2*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (5+(-2*d)) := by
    have he : (5+(-2*d))=(92/25:ℝ)+2*(d-31/50)^0*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have he : Saturated.slope d 0-Saturated.slope d 3=((-6*(d^2))+(5*d))/(5+(-2*d)) := by
    norm_num [Saturated.slope,Saturated.offset,auxLower]
    field_simp (disch := first | positivity | linarith) <;> ring
  rw [he]
  exact div_nonneg hn hden.le

theorem small_cap_3 {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    0 ≤ Saturated.offset d 3+auxLower*(Saturated.slope d 3-Saturated.slope d 0) := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ ((-103800*(d^2))+(41675*d)+(64548*(d^3))) := by
    have he : ((-103800*(d^2))+(41675*d)+(64548*(d^3)))=20646496*(d-31/50)^0*(33/50-d)^3+54064334*(d-31/50)^1*(33/50-d)^2+46595662*(d-31/50)^2*(33/50-d)^1+13242372*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (346875+(-397500*d)+(103500*(d^2))) := by
    have he : (346875+(-397500*d)+(103500*(d^2)))=(648048/5:ℝ)+6625500*(d-31/50)^0*(33/50-d)^2+6522000*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have he : Saturated.offset d 3+auxLower*(Saturated.slope d 3-Saturated.slope d 0)=((-103800*(d^2))+(41675*d)+(64548*(d^3)))/(346875+(-397500*d)+(103500*(d^2))) := by
    norm_num [Saturated.slope,Saturated.offset,auxLower]
    field_simp (disch := first | positivity | linarith) <;> ring
  rw [he]
  exact div_nonneg hn hden.le

theorem old_gain_small_width {d S : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hS : S ≤ auxLower) : Saturated.physicalGain d S 1=Saturated.slope d 0*S := by
  apply le_antisymm
  · have h := PR63Adaptation.fourGain_le (Saturated.slope d) (Saturated.offset d) S 1 0
    have hz : Saturated.offset d 0=0 := rfl
    rw [hz,zero_mul,add_zero] at h
    exact h
  · apply PR63Adaptation.fourGain_lower
    intro i
    fin_cases i
    · change Saturated.slope d 0*S ≤ Saturated.slope d 0*S+0*1
      simp
    · change Saturated.slope d 0*S ≤ Saturated.slope d 1*S+Saturated.offset d 1*1
      have hcap := small_cap_1 hd0 hd1
      have hslope := small_slope_1 hd0 hd1
      have hprod := mul_nonneg hslope (sub_nonneg.mpr hS)
      nlinarith only [hcap,hprod]
    · change Saturated.slope d 0*S ≤ Saturated.slope d 2*S+Saturated.offset d 2*1
      have hcap := small_cap_2 hd0 hd1
      have hslope := small_slope_2 hd0 hd1
      have hprod := mul_nonneg hslope (sub_nonneg.mpr hS)
      nlinarith only [hcap,hprod]
    · change Saturated.slope d 0*S ≤ Saturated.slope d 3*S+Saturated.offset d 3*1
      have hcap := small_cap_3 hd0 hd1
      have hslope := small_slope_3 hd0 hd1
      have hprod := mul_nonneg hslope (sub_nonneg.mpr hS)
      nlinarith only [hcap,hprod]

theorem gain_below_aux_width {d S : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hS : S ≤ auxLower) : physicalGain d S 1 ≤ Saturated.physicalGain d S 1 := by
  rw [old_gain_small_width hd0 hd1 hS]
  have h := FiniteGain.gain_le (slope d) (offset d) S 1 0
  have hz : offset d 0=0 := by norm_num [offset]
  have he : slope d 0=Saturated.slope d 0 := by
    norm_num [slope,Saturated.slope]
    field_simp (disch := linarith) <;> ring
  rw [hz,he,zero_mul,add_zero] at h
  exact h

theorem old_count_le_below_aux_width {d S : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hS : S ≤ auxLower) : PR63Adaptation.fullCount d S ≤ count d S := by
  have he := Saturated.physicalGain_rescale (d:=d) (S:=S) (D:=1)
    (by linarith) (by linarith) (by norm_num)
  norm_num only [div_one,one_mul] at he
  have h := gain_below_aux_width hd0 hd1 hS
  unfold count
  linarith only [he,h]

theorem weighted_short_fiber {d p S r m E : ℝ}
    (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (hp : p ≤ 1/2)
    (hlen : cutoff d S ≤ r+m)
    (hI : E ≤ 1-d*r-2*d*p*min S ((1-r)/2))
    (hold : E ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9))
    (haux : auxLower ≤ S → 81/200 ≤ m → m ≤ auxCutoff →
      E ≤ 1-2*d*m-2*d*p*min S (min auxUpper ((auxB-2*m)/auxLambda))) :
    E+2*d*p*S ≤ count d S+d*S := by
  by_cases hS : auxLower ≤ S
  · exact weighted_short_fiber_aux hd0 hd1 hp hS hlen hI hold (haux hS)
  · have hc := old_count_le_below_aux_width hd0 hd1 (le_of_not_ge hS)
    have ha : 0 ≤ 5/6-d := by linarith
    have ht : PR63Adaptation.cutoff d S ≤ cutoff d S :=
      div_le_div_of_nonneg_right (sub_le_sub_right hc (1/6)) ha
    have hh := PR63Adaptation.weighted_short_fiber (by linarith) (by linarith) hp
      (ht.trans hlen) hI hold
    linarith only [hh,hc]

theorem weighted_long_fiber {d p S r E : ℝ}
    (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (hp : p ≤ 1/2) (hS : 0 ≤ S)
    (hr : r ≤ cutoff d S) (hE : E ≤ 1/6+(5/6-d)*r) :
    E+2*d*p*S ≤ count d S+d*S := by
  have ha : 0 < 5/6-d := by linarith
  have ht : (5/6-d)*cutoff d S=count d S-1/6 := mul_div_cancel₀ _ ha.ne'
  have hh := mul_le_mul_of_nonneg_left hr ha.le
  have hs := mul_nonneg (mul_nonneg (show 0 ≤ d by linarith) hS)
    (show 0 ≤ 1-2*p by linarith)
  nlinarith only [ht,hh,hs,hE]

end Sil.Uneven.Bootstrap
end

/- Original module: Candidate.Uneven.BootstrapPowers. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Bootstrap

/-- Keep the detector length error explicit in the seven-case bound. -/
theorem fiber_exponent {d p S r m E loss eps : ℝ}
    (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hS : 0 ≤ S) (heps : 0 ≤ eps)
    (hlen : cutoff d S-eps ≤ r+m) (hrcap : r ≤ cutoff d S+eps)
    (hI : E ≤ max 1 ((1+5*r)/6)-d*r+loss)
    (hP : E ≤ 1-2*d*m+loss)
    (hIM : r < 1 → E ≤ 1-d*r-2*d*p*min S ((1-r)/2)+loss)
    (hPM : m ≤ 1/2 → E ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9)+loss)
    (haux : auxLower ≤ S → 81/200 ≤ m → m ≤ auxCutoff →
      E ≤ 1-2*d*m-2*d*p*min S (min auxUpper ((auxB-2*m)/auxLambda))+loss) :
    E+2*d*p*S ≤ count d S+d*S+loss+eps := by
  have hd : 0 ≤ d := by linarith
  have hdp : 0 ≤ 2*d*p := by positivity
  have hde : 0 ≤ d*eps := mul_nonneg hd heps
  by_cases hr : r < 1
  · have hi := hIM hr
    have hmin : min S ((1-(r+eps))/2) ≤ min S ((1-r)/2) :=
      min_le_min_left S (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hmin hdp
    have hi' : E-loss-d*eps ≤ 1-d*(r+eps)-2*d*p*min S ((1-(r+eps))/2) := by
      nlinarith only [hi,hmul]
    have ho : E-loss-d*eps ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9) := by
      by_cases hm : m ≤ 1/2
      · linarith only [hPM hm,hde]
      · have hn : min S (2*(1-2*m)/9) ≤ 0 := (min_le_right _ _).trans (by linarith)
        have hh := mul_nonpos_of_nonneg_of_nonpos hdp hn
        linarith only [hP,hde,hh]
    have ha : auxLower ≤ S → 81/200 ≤ m → m ≤ auxCutoff →
        E-loss-d*eps ≤ 1-2*d*m-2*d*p*min S (min auxUpper ((auxB-2*m)/auxLambda)) := by
      intro hS' hm0 hm1
      linarith only [haux hS' hm0 hm1,hde]
    have hh := weighted_short_fiber hd0 hd1 hp
      (show cutoff d S ≤ (r+eps)+m by linarith only [hlen]) hi' ho ha
    have hfee := mul_le_mul_of_nonneg_right (show d ≤ 1 by linarith) heps
    linarith only [hh,hfee]
  · rw [max_eq_right (by linarith : 1 ≤ (1+5*r)/6)] at hI
    have he : E-loss-(5/6-d)*eps ≤ 1/6+(5/6-d)*(r-eps) := by
      nlinarith only [hI]
    have hh := weighted_long_fiber hd0 hd1 hp hS
      (show r-eps ≤ cutoff d S by linarith only [hrcap]) he
    have hfee := mul_le_mul_of_nonneg_right (show 5/6-d ≤ 1 by linarith) heps
    linarith only [hh,hfee]

theorem count_from_powers {B A U d p S r m loss eps : ℝ}
    (hA : 0 < A) (hU : 1 < U) (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hS : 0 ≤ S) (heps : 0 ≤ eps)
    (hlen : cutoff d S-eps ≤ r+m) (hrcap : r ≤ cutoff d S+eps)
    (hI : B ≤ A*U^(max 1 ((1+5*r)/6)-d*r+loss))
    (hP : B ≤ A*U^(1-2*d*m+loss))
    (hIM : r < 1 → B ≤ A*U^(1-d*r-2*d*p*min S ((1-r)/2)+loss))
    (hPM : m ≤ 1/2 → B ≤ A*U^(1-2*d*m-2*d*p*min S (2*(1-2*m)/9)+loss))
    (haux : auxLower ≤ S → 81/200 ≤ m → m ≤ auxCutoff →
      B ≤ A*U^(1-2*d*m-2*d*p*min S (min auxUpper ((auxB-2*m)/auxLambda))+loss)) :
    B ≤ A*U^(count d S+d*S-2*d*p*S+loss+eps) := by
  by_cases hB : 0 < B
  · have hBA : 0 < B/A := div_pos hB hA
    have hlog (e : ℝ) (he : B ≤ A*U^e) : Real.logb U (B/A) ≤ e := by
      apply (Real.logb_le_iff_le_rpow hU hBA).mpr
      apply (div_le_iff₀ hA).mpr
      simpa only [mul_comm] using he
    have hh := fiber_exponent hd0 hd1 hp0 hp hS heps hlen hrcap
      (hlog _ hI) (hlog _ hP) (fun hr=>hlog _ (hIM hr)) (fun hm=>hlog _ (hPM hm))
      (fun hS' hm0 hm1=>hlog _ (haux hS' hm0 hm1))
    have he : Real.logb U (B/A) ≤ count d S+d*S-2*d*p*S+loss+eps := by linarith only [hh]
    have hb := (div_le_iff₀ hA).mp ((Real.logb_le_iff_le_rpow hU hBA).mp he)
    simpa only [mul_comm] using hb
  · exact (le_of_not_gt hB).trans (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _))

end Sil.Uneven.Bootstrap
end
