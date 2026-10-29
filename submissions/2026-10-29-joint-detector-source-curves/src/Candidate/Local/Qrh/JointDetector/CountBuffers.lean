/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.WordCount

/-! Finite parameter error bounds for the joint count. The algebraic domain
is `1/2 ≤ δ ≤ ν ≤ 3/4`; analytic norm calls retain their stricter cutoff. -/
namespace Qrh.JointDetector
noncomputable section

theorem count_den_pos {ν δ : ℝ} (hδν : δ ≤ ν) (hν : ν ≤ 3/4) :
    0 < 3-ν-2*δ := by linarith

theorem count_delta_difference {ν δ₁ δ₂ : ℝ}
    (hδ₁ : δ₁ ≤ ν) (hδ₂ : δ₂ ≤ ν) (hν : ν ≤ 3/4) :
    jointCountExponent ν δ₁-jointCountExponent ν δ₂ =
      3*(1-ν)^2*(δ₂-δ₁)/((3-ν-2*δ₁)*(3-ν-2*δ₂)) := by
  have hd1 := (count_den_pos hδ₁ hν).ne'
  have hd2 := (count_den_pos hδ₂ hν).ne'
  rw [jointCountExponent_eq, jointCountExponent_eq, div_sub_div _ _ hd1 hd2]
  congr 1
  ring

theorem count_nu_difference {ν₁ ν₂ δ : ℝ}
    (hδ₁ : δ ≤ ν₁) (hδ₂ : δ ≤ ν₂) (hν₁ : ν₁ ≤ 3/4) (hν₂ : ν₂ ≤ 3/4) :
    jointCountExponent ν₁ δ-jointCountExponent ν₂ δ =
      6*(1-δ)^2*(ν₂-ν₁)/((3-ν₁-2*δ)*(3-ν₂-2*δ)) := by
  have hd1 := (count_den_pos hδ₁ hν₁).ne'
  have hd2 := (count_den_pos hδ₂ hν₂).ne'
  rw [jointCountExponent_eq, jointCountExponent_eq, div_sub_div _ _ hd1 hd2]
  congr 1
  ring

theorem count_delta_lipschitz {ν δ₁ δ₂ : ℝ}
    (hδ₁ : δ₁ ≤ ν) (hδ₂ : δ₂ ≤ ν) (hν : ν ≤ 3/4) :
    |jointCountExponent ν δ₁-jointCountExponent ν δ₂| ≤ (1/3)*|δ₁-δ₂| := by
  have hd1 := count_den_pos hδ₁ hν
  have hd2 := count_den_pos hδ₂ hν
  have hb : 0 ≤ 1-ν := by linarith
  have h1 : 3*(1-ν) ≤ 3-ν-2*δ₁ := by linarith
  have h2 : 3*(1-ν) ≤ 3-ν-2*δ₂ := by linarith
  have hp := mul_le_mul h1 h2 (by positivity : 0 ≤ 3*(1-ν)) hd1.le
  have hc : 3*(1-ν)^2/((3-ν-2*δ₁)*(3-ν-2*δ₂)) ≤ 1/3 :=
    (div_le_iff₀ (mul_pos hd1 hd2)).2 (by nlinarith)
  calc
    _ = (3*(1-ν)^2/((3-ν-2*δ₁)*(3-ν-2*δ₂)))*|δ₁-δ₂| := by
      rw [count_delta_difference hδ₁ hδ₂ hν, abs_div, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 3*(1-ν)^2), abs_of_pos (mul_pos hd1 hd2),
        abs_sub_comm δ₂ δ₁]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)

theorem count_nu_lipschitz {ν₁ ν₂ δ : ℝ} (hδ : (1/2 : ℝ) ≤ δ)
    (hδ₁ : δ ≤ ν₁) (hδ₂ : δ ≤ ν₂) (hν₁ : ν₁ ≤ 3/4) (hν₂ : ν₂ ≤ 3/4) :
    |jointCountExponent ν₁ δ-jointCountExponent ν₂ δ| ≤ (24/25)*|ν₁-ν₂| := by
  have hd1 := count_den_pos hδ₁ hν₁
  have hd2 := count_den_pos hδ₂ hν₂
  have hb : 0 ≤ 1-δ := by linarith
  have h1 : (5/2)*(1-δ) ≤ 3-ν₁-2*δ := by linarith
  have h2 : (5/2)*(1-δ) ≤ 3-ν₂-2*δ := by linarith
  have hp := mul_le_mul h1 h2 (by positivity : 0 ≤ (5/2)*(1-δ)) hd1.le
  have hc : 6*(1-δ)^2/((3-ν₁-2*δ)*(3-ν₂-2*δ)) ≤ 24/25 :=
    (div_le_iff₀ (mul_pos hd1 hd2)).2 (by nlinarith)
  calc
    _ = (6*(1-δ)^2/((3-ν₁-2*δ)*(3-ν₂-2*δ)))*|ν₁-ν₂| := by
      rw [count_nu_difference hδ₁ hδ₂ hν₁ hν₂, abs_div, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 6*(1-δ)^2), abs_of_pos (mul_pos hd1 hd2),
        abs_sub_comm ν₂ ν₁]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)

/-- Both parameters can change without requiring a rectangular subdomain. -/
theorem count_two_parameter_lipschitz {ν₁ ν₂ δ₁ δ₂ : ℝ}
    (hδ₁ : (1/2 : ℝ) ≤ δ₁) (hδ₂ : (1/2 : ℝ) ≤ δ₂)
    (hd₁ : δ₁ ≤ ν₁) (hd₂ : δ₂ ≤ ν₂) (hν₁ : ν₁ ≤ 3/4) (hν₂ : ν₂ ≤ 3/4) :
    |jointCountExponent ν₁ δ₁-jointCountExponent ν₂ δ₂| ≤
      (1/3)*|δ₁-δ₂|+(24/25)*|ν₁-ν₂| := by
  rcases le_total ν₁ ν₂ with h | h
  · have htriangle := abs_sub_le (jointCountExponent ν₁ δ₁)
      (jointCountExponent ν₂ δ₁) (jointCountExponent ν₂ δ₂)
    have hnu := count_nu_lipschitz hδ₁ hd₁ (hd₁.trans h) hν₁ hν₂
    have hdelta := count_delta_lipschitz (hd₁.trans h) hd₂ hν₂
    linarith
  · have htriangle := abs_sub_le (jointCountExponent ν₁ δ₁)
      (jointCountExponent ν₁ δ₂) (jointCountExponent ν₂ δ₂)
    have hdelta := count_delta_lipschitz hd₁ (hd₂.trans h) hν₁
    have hnu := count_nu_lipschitz hδ₂ (hd₂.trans h) hd₂ hν₁ hν₂
    linarith

theorem count_exponent_lower {ν δ : ℝ} (hδν : δ ≤ ν) (hν : ν ≤ 3/4) :
    1-ν ≤ jointCountExponent ν δ := by
  rw [jointCountExponent_eq]
  apply (le_div_iff₀ (count_den_pos hδν hν)).2
  have h := mul_nonneg (show 0 ≤ 1-ν by linarith) (sub_nonneg.mpr hδν)
  nlinarith

theorem quarter_le_count_exponent {ν δ : ℝ} (hδν : δ ≤ ν) (hν : ν ≤ 3/4) :
    (1/4 : ℝ) ≤ jointCountExponent ν δ := by
  linarith [count_exponent_lower hδν hν]

/-- The joint/SC rate before taking the inherited zero-count minimum. -/
def detectorRate (ν δ : ℝ) : ℝ :=
  if δ ≤ ν then jointCountExponent ν δ else 1-δ

/-- Removing the internal zero-bin guard costs at most `2 e`, including the
branch where the amplitude slope is above the slightly lowered zero slope.
The analytic amplitude slope is not lowered or clipped in this argument. -/
theorem detectorRate_zero_buffer {ν δ e : ℝ} (hδ : (1/2 : ℝ) ≤ δ)
    (hν : ν ≤ 3/4) (he : 0 ≤ e) :
    detectorRate (ν-2*e) δ ≤ detectorRate ν δ+2*e := by
  by_cases hδeff : δ ≤ ν-2*e
  · have hδν : δ ≤ ν := by linarith
    simp only [detectorRate, ite_eq_left hδeff, ite_eq_left hδν]
    have h := count_nu_lipschitz hδ hδeff hδν (by linarith : ν-2*e ≤ 3/4) hν
    have ha : |ν-2*e-ν| = 2*e := by rw [abs_of_nonpos (by linarith)]; ring
    rw [ha] at h
    have hle := le_abs_self (jointCountExponent (ν-2*e) δ-jointCountExponent ν δ)
    linarith
  · by_cases hδν : δ ≤ ν
    · simp only [detectorRate, ite_eq_right hδeff, ite_eq_left hδν]
      have hlow := count_exponent_lower hδν hν
      linarith
    · simp only [detectorRate, ite_eq_right hδeff, ite_eq_right hδν]
      linarith

/-- Full energy error, including the changing ordinary-source term `ν P`.
The amplitude error is absolute (`s |Δδ|`), so it can be selected before the
eventual finite number of slots. -/
theorem count_full_energy_error {ν₁ ν₂ δ₁ δ₂ M P s Mmax Pmax sstar Eamp η : ℝ}
    (hδ₁ : (1/2 : ℝ) ≤ δ₁) (hδ₂ : (1/2 : ℝ) ≤ δ₂)
    (hd₁ : δ₁ ≤ ν₁) (hd₂ : δ₂ ≤ ν₂) (hν₁ : ν₁ ≤ 3/4) (hν₂ : ν₂ ≤ 3/4)
    (hM : M ∈ Set.Icc (0 : ℝ) Mmax) (hP : P ∈ Set.Icc (0 : ℝ) Pmax)
    (hsstar : 0 < sstar) (hs : sstar ≤ s) (_hEamp : 0 ≤ Eamp) (_hη : 0 ≤ η)
    (hamp : s*|δ₁-δ₂| ≤ Eamp) (hnu : |ν₁-ν₂| ≤ η) :
    |(jointCountExponent ν₁ δ₁*M+ν₁*P+δ₁*s)-
      (jointCountExponent ν₂ δ₂*M+ν₂*P+δ₂*s)| ≤
      (1+Mmax/(3*sstar))*Eamp+((24/25)*Mmax+Pmax)*η := by
  have hspos : 0 ≤ s := (hsstar.le.trans hs)
  have hMmax : 0 ≤ Mmax := hM.1.trans hM.2
  have hPmax : 0 ≤ Pmax := hP.1.trans hP.2
  have hdelta : |δ₁-δ₂| ≤ Eamp/sstar := (le_div_iff₀ hsstar).2 (by
    have h := mul_le_mul_of_nonneg_right hs (abs_nonneg (δ₁-δ₂))
    nlinarith)
  have hdeltaCost : (M/3)*|δ₁-δ₂|+s*|δ₁-δ₂| ≤ (1+Mmax/(3*sstar))*Eamp := by
    have h := mul_le_mul (div_le_div_of_nonneg_right hM.2 (by norm_num : (0 : ℝ) ≤ 3))
      hdelta (abs_nonneg _) (by positivity : 0 ≤ Mmax/3)
    calc
      _ ≤ (Mmax/3)*(Eamp/sstar)+Eamp := add_le_add h hamp
      _ = _ := by field_simp; ring
  have hnuCost : ((24/25)*M+P)*|ν₁-ν₂| ≤ ((24/25)*Mmax+Pmax)*η :=
    mul_le_mul (by nlinarith [hM.2, hP.2]) hnu (abs_nonneg _) (by positivity)
  have hcount := count_two_parameter_lipschitz hδ₁ hδ₂ hd₁ hd₂ hν₁ hν₂
  have he : |(jointCountExponent ν₁ δ₁-jointCountExponent ν₂ δ₂)*M+
      (ν₁-ν₂)*P+(δ₁-δ₂)*s| ≤
      |jointCountExponent ν₁ δ₁-jointCountExponent ν₂ δ₂| *M+|ν₁-ν₂| *P+|δ₁-δ₂| *s := by
    calc
      _ ≤ |(jointCountExponent ν₁ δ₁-jointCountExponent ν₂ δ₂)*M+(ν₁-ν₂)*P|+
          |(δ₁-δ₂)*s| := abs_add_le _ _
      _ ≤ (|(jointCountExponent ν₁ δ₁-jointCountExponent ν₂ δ₂)*M|+|(ν₁-ν₂)*P|)+
          |(δ₁-δ₂)*s| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hM.1,
          abs_of_nonneg hP.1, abs_of_nonneg hspos]
  have hcountM := mul_le_mul_of_nonneg_right hcount hM.1
  have hid : jointCountExponent ν₁ δ₁*M+ν₁*P+δ₁*s-
      (jointCountExponent ν₂ δ₂*M+ν₂*P+δ₂*s) =
      (jointCountExponent ν₁ δ₁-jointCountExponent ν₂ δ₂)*M+(ν₁-ν₂)*P+(δ₁-δ₂)*s := by ring
  rw [hid]
  nlinarith

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.count_two_parameter_lipschitz
#print axioms Qrh.JointDetector.count_full_energy_error
#print axioms Qrh.JointDetector.detectorRate_zero_buffer
