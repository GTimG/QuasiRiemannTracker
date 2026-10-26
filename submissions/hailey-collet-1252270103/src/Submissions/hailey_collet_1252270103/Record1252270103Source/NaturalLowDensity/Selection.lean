/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/Selection.lean. Original formulas and source attribution retained. -/
import Submissions.hailey_collet_1252270103.Record12518109Gain.Selection
import Submissions.hailey_collet_1252270103.Record1252270103Source.NaturalLowDensity.Homogeneous

set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.NaturalLowDensity
open Record12518109Gain
noncomputable section


theorem max_threshold_identity (x S : ℝ) (hS : 0 ≤ S) :
    max (x-S) (2*x-1) + max (x-S) ((9*x-2)/7)/2 =
      max (3*(x-S)/2) (max (x-S+(9*x-2)/14) (2*x-1+(9*x-2)/14)) := by
  by_cases hp : x-S ≤ (9*x-2)/7
  · rw [max_eq_right hp]
    by_cases hi : x-S ≤ 2*x-1
    · rw [max_eq_right hi, max_eq_right (by linarith : x-S+(9*x-2)/14 ≤ 2*x-1+(9*x-2)/14),
        max_eq_right (by linarith : 3*(x-S)/2 ≤ 2*x-1+(9*x-2)/14)]
      ring
    · rw [max_eq_left (le_of_not_ge hi),
        max_eq_left (by linarith : 2*x-1+(9*x-2)/14 ≤ x-S+(9*x-2)/14),
        max_eq_right (by linarith : 3*(x-S)/2 ≤ x-S+(9*x-2)/14)]
      ring
  · have hp' : (9*x-2)/7 ≤ x-S := le_of_not_ge hp
    have hi : 2*x-1 ≤ x-S := by linarith
    rw [max_eq_left hp',max_eq_left hi]
    have h1 : x-S+(9*x-2)/14 ≤ 3*(x-S)/2 := by linarith
    have h2 : 2*x-1+(9*x-2)/14 ≤ 3*(x-S)/2 := by linarith
    rw [max_eq_left (max_le h1 h2)]
    ring

theorem cutoff_balance {ν S : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4)
    (hS : 0 ≤ S) : cutoff ν S = inverseThreshold ν S + plainThreshold ν S/2 := by
  have hw : 0 < 5-6*ν := by linarith
  have hd0 : 0 < 15-6*ν := by linarith
  have hd1 : 0 < 115-54*ν := by linarith
  have hd2 : 0 < 185-138*ν := by linarith
  let x := xi ν S
  let z0 := 3*(x-S)/2
  let z1 := x-S+(9*x-2)/14
  let z2 := 2*x-1+(9*x-2)/14
  have hid0 : (5-6*ν)*(cutoff ν S-z0) = (15-6*ν)/2*(xi0 ν S-x) := by
    dsimp [cutoff,z0,xi0,x]
    field_simp (discharger := linarith)
    <;> ring
  have hid1 : (5-6*ν)*(cutoff ν S-z1) = (115-54*ν)/14*(xi1 ν S-x) := by
    dsimp [cutoff,z1,xi1,x]
    field_simp (discharger := linarith)
    <;> ring
  have hid2 : (5-6*ν)*(cutoff ν S-z2) = (185-138*ν)/14*(xi2 ν-x) := by
    dsimp [cutoff,z2,xi2,x]
    field_simp (discharger := linarith)
    <;> ring
  have hx0 : x ≤ xi0 ν S := min_le_left _ _
  have hx1 : x ≤ xi1 ν S := (min_le_right _ _).trans (min_le_left _ _)
  have hx2 : x ≤ xi2 ν := (min_le_right _ _).trans (min_le_right _ _)
  have hz0 : z0 ≤ cutoff ν S := by nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr hx0)]
  have hz1 : z1 ≤ cutoff ν S := by nlinarith [mul_nonneg hd1.le (sub_nonneg.mpr hx1)]
  have hz2 : z2 ≤ cutoff ν S := by nlinarith [mul_nonneg hd2.le (sub_nonneg.mpr hx2)]
  have he : cutoff ν S = max z0 (max z1 z2) := by
    apply le_antisymm
    · by_cases hx : xi0 ν S ≤ min (xi1 ν S) (xi2 ν)
      · have he : x = xi0 ν S := min_eq_left hx
        have hz : cutoff ν S = z0 := by rw [he] at hid0; nlinarith
        rw [hz]; exact le_max_left _ _
      · have he : x = min (xi1 ν S) (xi2 ν) := min_eq_right (le_of_not_ge hx)
        by_cases hy : xi1 ν S ≤ xi2 ν
        · rw [min_eq_left hy] at he
          have hz : cutoff ν S = z1 := by rw [he] at hid1; nlinarith
          rw [hz]; exact (le_max_left _ _).trans (le_max_right _ _)
        · rw [min_eq_right (le_of_not_ge hy)] at he
          have hz : cutoff ν S = z2 := by rw [he] at hid2; nlinarith
          rw [hz]; exact (le_max_right _ _).trans (le_max_right _ _)
    · exact max_le hz0 (max_le hz1 hz2)
  rw [he]
  exact (max_threshold_identity x S hS).symm

theorem xi_gain_identity {ν S : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) :
    rho ν-(1-ν*xi ν S) = gain ν S 1 := by
  have hv : 0 < ν := by linarith
  have hd : 5-2*ν ≠ 0 := by linarith
  have hd0 : 15-6*ν ≠ 0 := by linarith
  have hd1 : 115-54*ν ≠ 0 := by linarith
  have hd2 : 185-138*ν ≠ 0 := by linarith
  have h0 : rho ν-1+ν*xi0 ν S = phi ν*S := by
    unfold rho xi0 phi; field_simp (discharger := linarith) <;> ring
  have h1 : rho ν-1+ν*xi1 ν S = coeffA ν*S+coeffB ν := by
    apply mul_left_cancel₀ (mul_ne_zero hd hd1)
    unfold rho xi1 coeffA coeffB
    field_simp (discharger := linarith)
    <;> ring
  have h2 : rho ν-1+ν*xi2 ν = coeffC ν := by
    apply mul_left_cancel₀ (mul_ne_zero hd hd2)
    unfold rho xi2 coeffC
    field_simp (discharger := linarith)
    <;> ring
  dsimp [xi,gain]
  rw [mul_min_of_nonneg _ _ hv.le,mul_min_of_nonneg _ _ hv.le]
  simp only [mul_one]
  rw [show rho ν-(1-min (ν*xi0 ν S) (min (ν*xi1 ν S) (ν*xi2 ν))) =
    min (rho ν-1+ν*xi0 ν S) (min (rho ν-1+ν*xi1 ν S) (rho ν-1+ν*xi2 ν)) by
      simp only [min_add_add_left]; ring]
  rw [h0,h1,h2]

theorem selection_bounds {ν S : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4)
    (hS : 0 ≤ S) :
    0 < xi ν S ∧ xi ν S < 1 ∧ 1 ≤ cutoff ν S ∧ cutoff ν S ≤ 10/7 ∧
      3/4 < inverseThreshold ν S := by
  have hv : 0 < ν := by linarith
  have hw : 0 < 5-6*ν := by linarith
  have hd : 0 < 5-2*ν := by linarith
  have hd2 : 0 < 185-138*ν := by linarith
  have hx2 : xi2 ν < 1 := by unfold xi2; apply (div_lt_iff₀ hd2).mpr; linarith
  have hx : xi ν S < 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt hx2
  have hg := gain_nonneg hν0 hν1 hS (by norm_num : (0:ℝ) ≤ 1)
  have hid := xi_gain_identity (S:=S) hν0 hν1
  have hlow : 10/(3*(5-2*ν)) ≤ xi ν S := by
    dsimp [rho] at hid
    have hh : ν*(10/(3*(5-2*ν))-xi ν S) ≤ 0 := by
      have he : ν*(10/(3*(5-2*ν))) = 10*ν/(3*(5-2*ν)) := by ring
      nlinarith
    nlinarith
  have hlow' : 5/6 ≤ xi ν S := by
    have hh : (5/6:ℝ) ≤ 10/(3*(5-2*ν)) :=
      (le_div_iff₀ (by positivity : 0 < 3*(5-2*ν))).mpr (by linarith)
    exact hh.trans hlow
  have hmul : 10 ≤ 3*(5-2*ν)*xi ν S := by simpa only [mul_comm] using (div_le_iff₀ (show 0 < 3*(5-2*ν) by positivity)).mp hlow
  have hcutlo : 1 ≤ cutoff ν S := by
    unfold cutoff
    apply (le_div_iff₀ hw).mpr
    nlinarith
  have hcut : cutoff ν S ≤ 5/(5-2*ν) := by
    unfold cutoff
    rw [div_le_div_iff₀ hw hd]
    nlinarith
  have hcut' : (5:ℝ)/(5-2*ν) ≤ 10/7 := (div_le_iff₀ hd).mpr (by linarith)
  refine ⟨by linarith,hx,hcutlo,hcut.trans hcut',?_⟩
  have hthreshold : (22:ℝ)/29≤ inverseThreshold ν S := by
    by_cases hSsmall : S≤7/58
    · have hh0 : (22:ℝ)/29≤xi0 ν S-S := by
        unfold xi0
        have hd0 : 0<15-6*ν := by linarith
        rw [le_sub_iff_add_le,le_div_iff₀ hd0]
        nlinarith [mul_nonneg (show 0≤ν-1/2 by linarith) (show 0≤7/58-S by linarith)]
      have hh1 : (22:ℝ)/29≤xi1 ν S-S := by
        unfold xi1
        have hd1 : 0<115-54*ν := by linarith
        rw [le_sub_iff_add_le,le_div_iff₀ hd1]
        nlinarith [mul_nonneg (show 0≤ν-1/2 by linarith) (show 0≤7/58-S by linarith)]
      have hh2 : (22:ℝ)/29≤xi2 ν-S := by
        unfold xi2
        rw [le_sub_iff_add_le,le_div_iff₀ hd2]
        nlinarith [mul_nonneg (show 0≤ν-1/2 by linarith) (show 0≤7/58-S by linarith)]
      have hh : (22:ℝ)/29≤xi ν S-S := by
        dsimp [xi];rw [←min_sub_sub_right,←min_sub_sub_right];exact le_min hh0 (le_min hh1 hh2)
      exact hh.trans (le_max_left _ _)
    · have hSbig : 7/58≤S := le_of_not_ge hSsmall
      have hh0 : (51:ℝ)/58≤xi0 ν S := by
        unfold xi0
        apply (le_div_iff₀ (by linarith : 0<15-6*ν)).mpr
        nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hSbig)]
      have hh1 : (51:ℝ)/58≤xi1 ν S := by
        unfold xi1
        apply (le_div_iff₀ (by linarith : 0<115-54*ν)).mpr
        nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hSbig)]
      have hh2 : (51:ℝ)/58≤xi2 ν := by
        unfold xi2
        apply (le_div_iff₀ hd2).mpr
        linarith
      have hh : (51:ℝ)/58≤xi ν S := le_min hh0 (le_min hh1 hh2)
      exact (show (22:ℝ)/29≤2*xi ν S-1 by linarith).trans (le_max_right _ _)
  linarith

theorem count_cutoff_identity {ν S : ℝ} (hν1 : ν ≤ 3/4) :
    1-ν*xi ν S = 1/6+(5/6-ν)*cutoff ν S := by
  have hw : 5-6*ν ≠ 0 := by linarith
  apply mul_left_cancel₀ hw
  unfold cutoff
  field_simp (discharger := linarith)
  <;> ring

end
end QRH.Record1252270103Source.NaturalLowDensity
