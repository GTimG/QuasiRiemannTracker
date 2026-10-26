/- The exact marked gain `φ (2 min(S, u D) + min(S, v D))/3` of the inverse and plain caps `u`, `v` at
the frequency `D`, and the payment of a fee by the rate channel and the four affine forms of the gain.
From tracker PR #63 (Zhongpai Gao, `gao-balanced-marked-20261017`,
`Target830/Kernel/{ExactMarkedGain,ConservedWidthPayment}.lean`). Released under Apache 2.0. -/
import Mathlib.Tactic

set_option autoImplicit false

namespace Cycle63.Optimization.ExactGain

noncomputable section

/-- The gain `φ (2 min(S, u) + min(S, v))/3` of the live width `S` below the caps `u` and `v`. -/
def gain (phi u v S : ℝ) : ℝ := phi*(2*min S u + min S v)/3

/-- The gain of the live width `S` at the frequency `D`, with the caps `u D` and `v D`. -/
def scaledGain (phi u v S D : ℝ) : ℝ := gain phi (u*D) (v*D) S

theorem min_increment_le (S T cap : ℝ) (hST : S ≤ T) : min T cap - min S cap ≤ T - S := by
  rcases le_total cap S with hcap | hcap
  · rw [min_eq_right hcap, min_eq_right (hcap.trans hST)]
    linarith
  · rw [min_eq_left hcap]
    exact sub_le_sub_right (min_le_left _ _) S

theorem gain_zero (phi u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : gain phi u v 0 = 0 := by
  simp only [gain, min_eq_left hu, min_eq_left hv, mul_zero, add_zero, zero_div]

/-- The width less the gain at a rate `δ ≥ φ` grows with the width. -/
theorem deficit_mono {delta phi u v S T : ℝ} (hphi : 0 ≤ phi) (hphi_delta : phi ≤ delta)
    (hST : S ≤ T) : delta*S - gain phi u v S ≤ delta*T - gain phi u v T := by
  have hu := min_increment_le S T u hST
  have hv := min_increment_le S T v hST
  have hm := mul_le_mul_of_nonneg_left (show (2*min T u + min T v) - (2*min S u + min S v) ≤
    3*(T - S) by linarith) hphi
  have hd := mul_nonneg (sub_nonneg.mpr hphi_delta) (sub_nonneg.mpr hST)
  unfold gain
  nlinarith

theorem scaledGain_mono_width {phi u v D S T : ℝ} (hphi : 0 ≤ phi) (hST : S ≤ T) :
    scaledGain phi u v S D ≤ scaledGain phi u v T D := by
  have hu := min_le_min_right (u*D) hST
  have hv := min_le_min_right (v*D) hST
  unfold scaledGain gain
  gcongr

theorem scaledGain_mono_scale {phi u v S D E : ℝ} (hphi : 0 ≤ phi) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hDE : D ≤ E) : scaledGain phi u v S D ≤ scaledGain phi u v S E := by
  have hmu := min_le_min_left S (mul_le_mul_of_nonneg_left hDE hu)
  have hmv := min_le_min_left S (mul_le_mul_of_nonneg_left hDE hv)
  unfold scaledGain gain
  gcongr

/-- The gain is at most its capped form `φ (2 u + v) D/3`. -/
theorem scaledGain_le_capacity (phi u v S D : ℝ) (hphi : 0 ≤ phi) :
    scaledGain phi u v S D ≤ phi*(2*u + v)/3*D := by
  have hu := min_le_right S (u*D)
  have hv := min_le_right S (v*D)
  have hm := mul_le_mul_of_nonneg_left (show 2*min S (u*D) + min S (v*D) ≤ 2*(u*D) + v*D by linarith)
    hphi
  unfold scaledGain gain
  nlinarith

/-- The exact gain is the minimum of its four affine forms. -/
theorem scaledGain_eq_min_four (phi u v S F : ℝ) (hphi : 0 ≤ phi) :
    scaledGain phi u v S F =
      min (phi*S) (min (phi*(2*S + v*F)/3) (min (phi*(2*u*F + S)/3) (phi*(2*u + v)*F/3))) := by
  unfold scaledGain gain
  simp only [min_def]
  split_ifs <;> nlinarith

/-- One nonnegative affine form of the live width and frequency, with the removed width `R` charged
at the rate `γ`: the removed width costs `γ` and twice its frequency. -/
theorem affine_payment {gamma R a b S F : ℝ} (hgamma : 0 ≤ gamma) (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hF : 2*S ≤ F) :
    min (gamma*S) (a*S + b*F) ≤ gamma*R + a*max (S - R) 0 + b*max (F - 2*R) 0 := by
  by_cases hRS : S ≤ R
  · have hg := mul_le_mul_of_nonneg_left hRS hgamma
    have hposA : 0 ≤ a*max (S - R) 0 := mul_nonneg ha (le_max_right _ _)
    have hposB : 0 ≤ b*max (F - 2*R) 0 := mul_nonneg hb (le_max_right _ _)
    exact (min_le_left _ _).trans (by linarith)
  · have hRS' : R ≤ S := le_of_lt (lt_of_not_ge hRS)
    rw [max_eq_left (by linarith : 0 ≤ S - R), max_eq_left (by linarith : 0 ≤ F - 2*R)]
    by_cases hslope : a + 2*b ≤ gamma
    · have hs := mul_nonneg (by linarith : 0 ≤ gamma - a - 2*b) hR
      exact (min_le_right _ _).trans (by nlinarith)
    · have hs := mul_nonneg (by linarith : 0 ≤ a + 2*b - gamma) (by linarith : 0 ≤ S - R)
      have htail := mul_nonneg hb (by linarith : 0 ≤ F - 2*S)
      exact (min_le_left _ _).trans (by nlinarith)

/-- If the rate channel `base + γ S` and the four affine forms of the gain at the supplied width `S`
and the frequency `F` keep the fee, then so does `base + γ R` plus the gain of the live width and the
live frequency, for every removed width `R` with `S ≤ R + live` and `F ≤ 2 R + freq`, provided the
rate `γ` is at least twice the slope `φ (2 u + v)/3` of the capped gain: a negative live frequency
makes the gain its capped form, and the removed width then pays it. -/
theorem exact_gain_payment {gamma R phi u v S F live freq base fee : ℝ}
    (hgamma : 0 ≤ gamma) (hR : 0 ≤ R) (hphi : 0 ≤ phi) (hu : 0 ≤ u) (hv : 0 ≤ v) (hF : 2*S ≤ F)
    (hslope : 2*(phi*(2*u + v)/3) ≤ gamma) (hlive : 0 ≤ live) (hsupply : S ≤ R + live)
    (hfrequency : F ≤ 2*R + freq)
    (hrate : fee ≤ base + gamma*S) (hlinear : fee ≤ base + phi*S)
    (hmixed : fee ≤ base + phi*(2*S + v*F)/3) (hinverse : fee ≤ base + phi*(2*u*F + S)/3)
    (hcapped : fee ≤ base + phi*(2*u + v)*F/3) :
    fee ≤ base + gamma*R + scaledGain phi u v live freq := by
  have hc : 0 ≤ phi*(2*u + v)/3 := by positivity
  rcases lt_or_ge freq 0 with hneg | hfreq
  · have hg : scaledGain phi u v live freq = phi*(2*u + v)/3*freq := by
      unfold scaledGain gain
      rw [min_eq_right (by nlinarith : u*freq ≤ live), min_eq_right (by nlinarith : v*freq ≤ live)]
      ring
    rw [hg]
    have h1 := mul_le_mul_of_nonneg_left (show F - 2*R ≤ freq by linarith) hc
    have h2 := mul_nonneg (sub_nonneg.mpr hslope) (show 0 ≤ R - F/2 by linarith)
    have h3 := mul_nonneg hgamma (show 0 ≤ F/2 - S by linarith)
    nlinarith
  have pay (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbranch : fee ≤ base + a*S + b*F) :
      fee ≤ base + gamma*R + a*max (S - R) 0 + b*max (F - 2*R) 0 := by
    have hm : fee - base ≤ min (gamma*S) (a*S + b*F) := le_min (by linarith) (by linarith)
    have hp := affine_payment hgamma hR ha hb hF
    linarith
  have h0 := pay phi 0 hphi le_rfl (by linarith)
  have h1 := pay (2*phi/3) (phi*v/3) (by positivity) (by positivity) (by linarith)
  have h2 := pay (phi/3) (2*phi*u/3) (by positivity) (by positivity) (by linarith)
  have h3 := pay 0 (phi*(2*u + v)/3) le_rfl (by positivity) (by linarith)
  have hL : max (S - R) 0 ≤ live := max_le (by linarith) hlive
  have hV : max (F - 2*R) 0 ≤ freq := max_le (by linarith) hfreq
  have hmono := (scaledGain_mono_width (D := max (F - 2*R) 0) (u := u) (v := v) hphi hL).trans
    (scaledGain_mono_scale (S := live) hphi hu hv hV)
  have hmin : fee - (base + gamma*R) ≤ scaledGain phi u v (max (S - R) 0) (max (F - 2*R) 0) := by
    rw [scaledGain_eq_min_four _ _ _ _ _ hphi]
    refine le_min ?_ (le_min ?_ (le_min ?_ ?_)) <;> nlinarith
  linarith

end

end Cycle63.Optimization.ExactGain
