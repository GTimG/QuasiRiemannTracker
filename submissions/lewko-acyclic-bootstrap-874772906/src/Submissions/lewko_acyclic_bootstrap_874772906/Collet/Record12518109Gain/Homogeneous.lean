import Mathlib.Tactic

/-! Homogeneous marked gain from CLOSED_PROOF §16 and PROOF_EXTENSION (R5–R6).
Human author: Hailey Collet. Apache-2.0. -/

namespace Record12518109Gain
noncomputable section

def rho (ν : ℝ) := 1 - 10*ν/(3*(5-2*ν))
def phi (ν : ℝ) := ν*(5-6*ν)/(5-2*ν)
def coeffA (ν : ℝ) := 14*ν*(5-6*ν)/(115-54*ν)
def coeffB (ν : ℝ) := 2*ν*(5-6*ν)^2/(3*(5-2*ν)*(115-54*ν))
def coeffC (ν : ℝ) := 16*ν*(5-6*ν)^2/(3*(5-2*ν)*(185-138*ν))
def gain (ν S F : ℝ) := min (phi ν*S) (min (coeffA ν*S+coeffB ν*F) (coeffC ν*F))

theorem coefficient_bounds {ν : ℝ} (hν0 : 31/50 ≤ ν) (hν1 : ν ≤ 3/4) :
    0 < phi ν ∧ phi ν ≤ ν ∧ 0 < coeffA ν ∧ coeffA ν < phi ν ∧
      0 < coeffB ν ∧ coeffB ν < coeffC ν ∧ coeffC ν < 1/50 := by
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
  have hsmall : coeffC ν < 1/50 := by
    have hn : ν*(5-6*ν) ≤ 4/5 := by nlinarith [sq_nonneg (ν-31/50)]
    have hn0 : 0 ≤ ν*(5-6*ν) := by positivity
    have hn' := mul_le_mul hn (show 5-6*ν ≤ 32/25 by linarith) hw.le (by norm_num : (0:ℝ) ≤ 4/5)
    have hden := mul_le_mul (show (7/2:ℝ) ≤ 5-2*ν by linarith)
      (show (163/2:ℝ) ≤ 185-138*ν by linarith) (by norm_num : (0:ℝ) ≤ 163/2) hd.le
    unfold coeffC
    apply (div_lt_iff₀ (by positivity : 0 < 3*(5-2*ν)*(185-138*ν))).mpr
    nlinarith
  exact ⟨hp,hpp,hap,hal,hb,hbl,hsmall⟩

theorem gain_nonneg {ν S F : ℝ} (hν0 : 31/50 ≤ ν) (hν1 : ν ≤ 3/4)
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

theorem gain_mono {ν S F T Q : ℝ} (hν0 : 31/50 ≤ ν) (hν1 : ν ≤ 3/4)
    (hS : S ≤ T) (hF : F ≤ Q) : gain ν S F ≤ gain ν T Q := by
  obtain ⟨hp,_,ha,_,hb,hbc,_⟩ := coefficient_bounds hν0 hν1
  apply min_le_min (mul_le_mul_of_nonneg_left hS hp.le)
  apply min_le_min
  · exact add_le_add (mul_le_mul_of_nonneg_left hS ha.le) (mul_le_mul_of_nonneg_left hF hb.le)
  · exact mul_le_mul_of_nonneg_left hF (hb.trans hbc).le

theorem gain_width_loss {ν S q F : ℝ} (hν0 : 31/50 ≤ ν) (hν1 : ν ≤ 3/4)
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

theorem gain_slot_loss {ν S T F : ℝ} (hν0 : 31/50 ≤ ν) (hν1 : ν ≤ 3/4)
    (hS : S ≤ T) : gain ν T F - phi ν*(T-S) ≤ gain ν S F := by
  obtain ⟨hp,_,ha,hap,_,_,_⟩ := coefficient_bounds hν0 hν1
  have h0 := mul_nonneg hp.le (sub_nonneg.mpr hS)
  have h1 := mul_le_mul_of_nonneg_right hap.le (sub_nonneg.mpr hS)
  apply le_min
  · linarith [gain_le_phi ν T F]
  · apply le_min
    · linarith [gain_le_middle ν T F]
    · linarith [gain_le_C ν T F]

theorem weighted_exponent_mono {ν S T F : ℝ} (hν0 : 31/50 ≤ ν)
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

theorem root_series_gap {ν : ℝ} (hν0 : 31/50 ≤ ν) (hν1 : ν ≤ 3/4) :
    279/175 < 6*(rho ν-coeffC ν) ∧ 83/2100 < (rho ν-1/6)/2-coeffC ν := by
  have hr := rho_lower hν1
  have hc := (coefficient_bounds hν0 hν1).2.2.2.2.2.2
  constructor <;> linarith

end
end Record12518109Gain
