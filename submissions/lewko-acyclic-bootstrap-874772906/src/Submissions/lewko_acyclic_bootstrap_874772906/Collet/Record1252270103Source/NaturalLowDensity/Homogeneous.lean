/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/Homogeneous.lean. Original formulas and source attribution retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Homogeneous
import Mathlib.Tactic

/-! Homogeneous marked gain from CLOSED_PROOF §16 and PROOF_EXTENSION (R5–R6).
Human author: Hailey Collet. Apache-2.0. -/

set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.NaturalLowDensity
open Record12518109Gain
noncomputable section


theorem coefficient_bounds {ν : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) :
    0 < phi ν ∧ phi ν ≤ ν ∧ 0 < coeffA ν ∧ coeffA ν < phi ν ∧
      0 < coeffB ν ∧ coeffB ν < coeffC ν ∧ coeffC ν < 1/40 := by
  have hv : 0 < ν := by linarith
  have hw : 0 < 5-6*ν := by linarith
  have hd : 0 < 5-2*ν := by linarith
  have ha : 0 < 115-54*ν := by linarith
  have hc : 0 < 185-138*ν := by linarith
  have hp : 0 < phi ν := div_pos (mul_pos hv hw) hd
  have hpp : phi ν ≤ ν := (div_le_iff₀ hd).mpr (by nlinarith)
  have hap : 0 < coeffA ν := div_pos (by positivity) ha
  have hb : 0 < coeffB ν := div_pos (by positivity) (by positivity)
  have hcc : 0 < coeffC ν := div_pos (by positivity) (by positivity)
  have hal : coeffA ν < phi ν := by
    unfold coeffA phi
    rw [div_lt_div_iff₀ ha hd]
    have hpos := mul_pos (mul_pos hv hw) (show 0 < 45-26*ν by linarith)
    nlinarith
  have hbl : coeffB ν < coeffC ν := by
    unfold coeffB coeffC
    rw [div_lt_div_iff₀ (by positivity : 0 < 3*(5-2*ν)*(115-54*ν))
      (by positivity : 0 < 3*(5-2*ν)*(185-138*ν))]
    have hpos := mul_pos (mul_pos hv (sq_pos_of_pos hw))
      (mul_pos hd (show 0 < 735-294*ν by linarith))
    nlinarith
  have hsmall : coeffC ν < 1/40 := by
    let x := ν-1/2
    have hx : 0≤x := by dsimp [x];linarith
    have hx' : 0≤1/4-x := by dsimp [x];linarith
    have hid : 3*(5-2*ν)*(185-138*ν)-40*(16*ν*(5-6*ν)^2)=
        112+2495*x+1092*x*(1/4-x)+23040*x^2*(1/4-x) := by dsimp [x];ring
    have hpos : 0<3*(5-2*ν)*(185-138*ν)-40*(16*ν*(5-6*ν)^2) := by
      rw [hid];positivity
    unfold coeffC
    apply (div_lt_iff₀ (by positivity : 0 < 3*(5-2*ν)*(185-138*ν))).mpr
    linarith
  exact ⟨hp,hpp,hap,hal,hb,hbl,hsmall⟩

theorem gain_nonneg {ν S F : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4)
    (hS : 0 ≤ S) (hF : 0 ≤ F) : 0 ≤ gain ν S F := by
  obtain ⟨hp,_,ha,_,hb,hbc,_⟩ := coefficient_bounds hν0 hν1
  exact le_min (mul_nonneg hp.le hS) (le_min (by positivity)
    (mul_nonneg (hb.trans hbc).le hF))

theorem gain_le_phi (ν S F : ℝ) : gain ν S F ≤ phi ν*S := min_le_left _ _
theorem gain_le_middle (ν S F : ℝ) : gain ν S F ≤ coeffA ν*S+coeffB ν*F :=
  (min_le_right _ _).trans (min_le_left _ _)
theorem gain_le_C (ν S F : ℝ) : gain ν S F ≤ coeffC ν*F :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem gain_homogeneous (ν S F k : ℝ) (hk : 0 ≤ k) :
    gain ν (k*S) (k*F) = k*gain ν S F := by
  unfold gain
  rw [mul_min_of_nonneg _ _ hk, mul_min_of_nonneg _ _ hk]
  congr 1
  · ring
  · congr 1 <;> ring

theorem gain_mono {ν S F T Q : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4)
    (hS : S ≤ T) (hF : F ≤ Q) : gain ν S F ≤ gain ν T Q := by
  obtain ⟨hp,_,ha,_,hb,hbc,_⟩ := coefficient_bounds hν0 hν1
  apply min_le_min (mul_le_mul_of_nonneg_left hS hp.le)
  apply min_le_min
  · exact add_le_add (mul_le_mul_of_nonneg_left hS ha.le) (mul_le_mul_of_nonneg_left hF hb.le)
  · exact mul_le_mul_of_nonneg_left hF (hb.trans hbc).le

theorem gain_width_loss {ν S q F : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4)
    (hq : q ≤ F) : gain ν S F - coeffC ν*(F-q) ≤ gain ν S q := by
  obtain ⟨_,_,_,_,hb,hbc,_⟩ := coefficient_bounds hν0 hν1
  have hc := (hb.trans hbc).le
  have h0 := mul_nonneg hc (sub_nonneg.mpr hq)
  have h1 := mul_le_mul_of_nonneg_right hbc.le (sub_nonneg.mpr hq)
  apply le_min
  · linarith [gain_le_phi ν S F]
  · apply le_min
    · linarith [gain_le_middle ν S F]
    · linarith [gain_le_C ν S F]

theorem gain_slot_loss {ν S T F : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4)
    (hS : S ≤ T) : gain ν T F - phi ν*(T-S) ≤ gain ν S F := by
  obtain ⟨hp,_,ha,hap,_,_,_⟩ := coefficient_bounds hν0 hν1
  have h0 := mul_nonneg hp.le (sub_nonneg.mpr hS)
  have h1 := mul_le_mul_of_nonneg_right hap.le (sub_nonneg.mpr hS)
  apply le_min
  · linarith [gain_le_phi ν T F]
  · apply le_min
    · linarith [gain_le_middle ν T F]
    · linarith [gain_le_C ν T F]

theorem weighted_exponent_mono {ν S T F : ℝ} (hν0 : 1/2 ≤ ν)
    (hν1 : ν ≤ 3/4) (hS : S ≤ T) :
    ν*S-gain ν S F ≤ ν*T-gain ν T F := by
  have hh := gain_slot_loss (F:=F) hν0 hν1 hS
  have hphi := (coefficient_bounds hν0 hν1).2.1
  have hm := mul_le_mul_of_nonneg_right hphi (sub_nonneg.mpr hS)
  linarith

theorem rho_lower {ν : ℝ} (hν : ν ≤ 3/4) : 2/7 ≤ rho ν := by
  have hd : 0 < 3*(5-2*ν) := by linarith
  unfold rho
  have hh : 10*ν/(3*(5-2*ν)) ≤ 5/7 := (div_le_iff₀ hd).mpr (by linarith)
  linarith

theorem root_series_gap {ν : ℝ} (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) :
    279/175 < 6*(rho ν-coeffC ν) ∧ 83/2100 < (rho ν-1/6)/2-coeffC ν := by
  let D := 3*(5-2*ν)*(185-138*ν)
  let y := 3/4-ν
  have hy : 0≤y := by dsimp [y];linarith
  have hd : 0<5-2*ν := by linarith
  have hc : 0<185-138*ν := by linarith
  have hD : 0<D := by dsimp [D];positivity
  have hid₁ : 175*D*(6*(rho ν-coeffC ν)-279/175)=
      59283/4+1191798*y+1734588*y^2+604800*y^3 := by
    dsimp [D,y,rho,coeffC]
    field_simp (discharger := linarith)
    <;> ring
  have hid₂ : 350*D*((rho ν-1/6)/2-coeffC ν-83/2100)=
      19761/4+193516*y+233196*y^2+201600*y^3 := by
    dsimp [D,y,rho,coeffC]
    field_simp (discharger := linarith)
    <;> ring
  have hp₁ : 0<175*D*(6*(rho ν-coeffC ν)-279/175) := by rw [hid₁];positivity
  have hp₂ : 0<350*D*((rho ν-1/6)/2-coeffC ν-83/2100) := by rw [hid₂];positivity
  have hh₁ : 0<6*(rho ν-coeffC ν)-279/175 :=
    (mul_pos_iff_of_pos_left (by positivity : 0<175*D)).mp hp₁
  have hh₂ : 0<(rho ν-1/6)/2-coeffC ν-83/2100 :=
    (mul_pos_iff_of_pos_left (by positivity : 0<350*D)).mp hp₂
  constructor <;> linarith

end
end QRH.Record1252270103Source.NaturalLowDensity
