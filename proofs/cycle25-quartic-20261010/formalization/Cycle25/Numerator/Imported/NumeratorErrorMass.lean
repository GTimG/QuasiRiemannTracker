import Cycle25.Numerator.Imported.NumeratorUnramifiedMass

/-! Absolute coefficient bounds for the quotient-free local errors. -/
noncomputable section
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

def ramifiedErrorCoefficients (eta a rho x z : ℂ) (j : ℕ) : CubicCoefficients :=
  let c := ramifiedRegularCoefficients p hp hg eta a rho x z j
  let d := ramifiedStrictCoefficient p hp hg eta a rho x z j
  ⟨c.a, c.b + d, c.c, 0⟩

theorem ramified_error_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j =
      (ramifiedErrorCoefficients p hp hg eta a rho x z j).eval
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hr := ramified_regular_expansion p hp hg eta a rho x w z j
  have hs := ramified_strict_expansion p hp hg eta a rho x w z j
  rw [hs] at hr
  dsimp only [ramifiedErrorCoefficients,CubicCoefficients.eval,cubic]
  rw [eq_add_of_sub_eq hr]
  dsimp only [QuadraticCoefficients.eval,quadratic]
  ring

theorem ramified_error_mass_le (eta a rho x z : ℂ) (j : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (ramifiedErrorCoefficients p hp hg eta a rho x z j).mass r ≤
      (ramifiedRegularCoefficients p hp hg eta a rho x z j).mass r +
      ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ * r := by
  dsimp only [ramifiedErrorCoefficients,CubicCoefficients.mass,cubicMass,
    QuadraticCoefficients.mass,quadraticMass]
  simp only [norm_zero,zero_mul,add_zero]
  have hh := mul_le_mul_of_nonneg_right
    (norm_add_le (ramifiedRegularCoefficients p hp hg eta a rho x z j).b
      (ramifiedStrictCoefficient p hp hg eta a rho x z j)) hr
  linarith

/-- Only repeated ramified labels cost a factor Q^rho on the left line. -/
theorem ramified_error_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a phase x z : ℂ) (alpha eps rho : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hphase : phase ^ 6 = 1)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho) (j : ℕ) (hj : j < 6) :
    (ramifiedErrorCoefficients p hp hg eta a phase x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(1 / 2 - rho))) ≤
      1161 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ) *
        (if 2 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ rho else 1) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0 < Q := by dsimp only [Q]; linarith
  have hQ1 : 1 ≤ Q := by dsimp only [Q]; linarith
  have hR := ramified_regular_coefficient_mass p hp hg hc eta a phase x z
    alpha eps (1 / 2 - rho) hQ heta ha hphase halpha halpha1 heps heps1 hx hz hline j hj
  have hM := ramified_error_mass_le p hp hg eta a phase x z j
    (Q ^ (-(1 / 2 - rho))) (Real.rpow_nonneg hQ0.le _)
  have hx' : (51 / 100 : ℝ) ≤ x.re := by rw [hx]; linarith
  have hz' : (17 / 50 : ℝ) ≤ z.re := hz.ge
  by_cases hj2 : 2 ≤ j
  · rw [if_pos hj2]
    have hS := ramified_strict_coefficient_mass p hp hg hc eta a phase x z
      (1 / 2 - rho) hQ heta ha hphase hx' hz' j hj
    have he : Q ^ (1 - (1 / 2 - rho)) = Q ^ (1 / 2 : ℝ) * Q ^ rho := by
      rw [←Real.rpow_add hQ0]
      congr 1
      ring
    change _ ≤ 6 * Q ^ (1 - (1 / 2 - rho)) at hS
    rw [he] at hS
    have hpow : 1 ≤ Q ^ rho := Real.one_le_rpow hQ1 hrho
    change _ ≤ 1161 * Q ^ (1 / 2 : ℝ) * Q ^ rho
    change _ ≤ 1155 * Q ^ (1 / 2 : ℝ) at hR
    nlinarith [Real.rpow_nonneg hQ0.le (1 / 2 : ℝ)]
  · rw [if_neg hj2,mul_one]
    have hS := ramified_boundary_coefficient_mass p hp hg hc eta a phase x z
      (1 / 2 - rho) hQ heta ha hphase hx' hz' j (by omega)
    have hpow : Q ^ (-(1 / 2 - rho)) ≤ Q ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    change _ ≤ 6 * Q ^ (-(1 / 2 - rho)) at hS
    change _ ≤ 1155 * Q ^ (1 / 2 : ℝ) at hR
    change _ ≤ 1161 * Q ^ (1 / 2 : ℝ)
    linarith

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
