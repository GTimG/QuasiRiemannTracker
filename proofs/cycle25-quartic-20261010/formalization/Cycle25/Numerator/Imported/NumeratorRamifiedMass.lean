import Cycle25.Numerator.Imported.NumeratorPolynomialMass
import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrictSelected

/-! Actual coefficient bounds for ramified local errors.  The certified original
regular-error estimate is uniform on a vertical line.  Exact finite-degree
extraction turns that estimate into the coefficient bound needed before the
physical numerator is reconstructed. -/
noncomputable section
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

structure QuadraticCoefficients where
  a : ℂ
  b : ℂ
  c : ℂ

def QuadraticCoefficients.eval (c : QuadraticCoefficients) (T : ℂ) : ℂ :=
  quadratic c.a c.b c.c T
def QuadraticCoefficients.mass (c : QuadraticCoefficients) (r : ℝ) : ℝ :=
  quadraticMass c.a c.b c.c r

def ramifiedRegularCoefficients (eta a rho x z : ℂ) (j : ℕ) : QuadraticCoefficients :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  let X := Q ^ (-x)
  let B := star eta * Q ^ x
  let P₀ := rowClosedMarked p hp hg eta a X 0 V rho j
  let P₁ := rowClosedMarked p hp hg eta a X 1 V rho j - P₀
  let S := B * (1 - V) *
    (rowMarkedTerm p hp hg eta a X 1 V rho j 1 0 1 0 /
      (1 - evenRatio (Ideal.absNorm (Ideal.span {p})) a X V))
  ⟨B * (1 - V) * P₀,
    B * (1 - V) * P₁ - 1 - (1 - V) * P₀ - S,
    -(1 - V) * P₁⟩

theorem ramified_regular_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j -
      ramifiedStrictSelected p hp hg eta a rho x w z j =
    (ramifiedRegularCoefficients p hp hg eta a rho x z j).eval
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hP := rowClosedMarked_affine p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j
  have hT := rowMarkedTerm_monomial p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0
  unfold ramifiedSelected ramifiedStrictSelected ramifiedClosed
  rw [hP, hT]
  simp only [pow_one]
  unfold QuadraticCoefficients.eval ramifiedRegularCoefficients quadratic
  ring

/-- No analytic estimate is assumed here: this coefficient mass follows from the
original regular-error theorem, applied on the complete old vertical line. -/
theorem ramified_regular_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (alpha eps sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hsigma : 1 - alpha - 6 * eps ≤ sigma) (j : ℕ) (hj : j < 6) :
    (ramifiedRegularCoefficients p hp hg eta a rho x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma)) ≤
      1155 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ) := by
  let c := ramifiedRegularCoefficients p hp hg eta a rho x z j
  have hb := quadraticMass_le_of_vertical_bound
    (Ideal.absNorm (Ideal.span {p}) : ℝ) (1 - alpha - 6 * eps) sigma
    (385 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 / 2 : ℝ))
    c.a c.b c.c (by linarith) hsigma (by
      intro w hw
      have hh := ramifiedSelected_central_regular p hp hg hc eta a rho x w z
        alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j hj
      rw [ramified_regular_expansion p hp hg] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  nlinarith

def ramifiedStrictCoefficient (eta a rho x z : ℂ) (j : ℕ) : ℂ :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  star eta * Q ^ x * (1 - V) *
    (rowMarkedTerm p hp hg eta a (Q ^ (-x)) 1 V rho j 1 0 1 0 /
      (1 - evenRatio (Ideal.absNorm (Ideal.span {p})) a (Q ^ (-x)) V))

theorem ramified_strict_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedStrictSelected p hp hg eta a rho x w z j =
      ramifiedStrictCoefficient p hp hg eta a rho x z j *
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w) := by
  have ht := rowMarkedTerm_monomial p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0
  unfold ramifiedStrictSelected ramifiedStrictCoefficient
  rw [ht]
  simp only [pow_one]
  ring

/-- The only large coefficient is the original strict ramified coefficient. -/
theorem ramified_strict_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (j : ℕ) (hj : j < 6) :
    ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ *
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) ≤
      6 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (1 - sigma) := by
  have hh := ramifiedStrictSelected_central_norm p hp hg hc eta a rho x
    (sigma : ℂ) z hQ heta ha hρ hx hz j hj
  rw [ramified_strict_expansion p hp hg, norm_mul,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith :
      (0 : ℝ) < Ideal.absNorm (Ideal.span {p})), Complex.neg_re, Complex.ofReal_re] at hh
  exact hh

theorem ramified_boundary_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (j : ℕ) (hj : j ≤ 1) :
    ‖ramifiedStrictCoefficient p hp hg eta a rho x z j‖ *
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) ≤
      6 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma) := by
  have hh := ramifiedStrictSelected_boundary_norm p hp hg hc eta a rho x
    (sigma : ℂ) z hQ heta ha hρ hx hz j hj
  rw [ramified_strict_expansion p hp hg, norm_mul,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith :
      (0 : ℝ) < Ideal.absNorm (Ideal.span {p})), Complex.neg_re, Complex.ofReal_re] at hh
  exact hh

def ramifiedCorrectionCoefficients (eta a rho x z : ℂ) (j : ℕ) : QuadraticCoefficients :=
  let Q : ℂ := Ideal.absNorm (Ideal.span {p})
  let V := coordV (Ideal.absNorm (Ideal.span {p})) z
  let P₀ := rowClosedMarked p hp hg eta a (Q ^ (-x)) 0 V rho j
  let P₁ := rowClosedMarked p hp hg eta a (Q ^ (-x)) 1 V rho j - P₀
  ⟨1 + (1 - V) * P₀, (1 - V) * P₁, 0⟩

theorem ramified_correction_expansion (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedClosed p hp hg eta a rho x w z j =
      (ramifiedCorrectionCoefficients p hp hg eta a rho x z j).eval
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)) := by
  have hh := rowClosedMarked_affine p hp hg eta a
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j
  unfold ramifiedClosed
  rw [hh]
  unfold ramifiedCorrectionCoefficients QuadraticCoefficients.eval quadratic
  ring

theorem ramified_correction_coefficient_mass
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (eta a rho x z : ℂ) (sigma : ℝ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hxw : 1 ≤ x.re + sigma)
    (j : ℕ) (hj : j < 6) :
    (ramifiedCorrectionCoefficients p hp hg eta a rho x z j).mass
      ((Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-sigma)) ≤ 579 := by
  let c := ramifiedCorrectionCoefficients p hp hg eta a rho x z j
  have hb := quadraticMass_le_of_vertical_bound
    (Ideal.absNorm (Ideal.span {p}) : ℝ) sigma sigma 193 c.a c.b c.c
    (by linarith) le_rfl (by
      intro w hw
      have hh := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z
        hQ heta ha hρ hx (by rw [hw]; exact hsigma) hz (by rw [hw]; exact hxw) j hj
      rw [ramified_correction_expansion p hp hg] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  norm_num only [show (3 : ℝ) * 193 = 579 by norm_num] at hb
  exact hb

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
