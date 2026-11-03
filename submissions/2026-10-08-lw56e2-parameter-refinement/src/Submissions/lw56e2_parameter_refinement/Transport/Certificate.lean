/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/Certificate.lean
Original SHA-256: 5dba64a1d2dc6ae6c7452626bd8a4d0218441b5e818b6e7da4426d4523f1e238
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.Candidate
import Submissions.lw56e2_parameter_refinement.Transport.Endpoint

/-!
# Joined parameter certificate

This connects the independently named candidate and endpoint constants and
extends the endpoint inequality over the buffered row-scale interval. It
certifies a real exponent expression; the estimate for actual arithmetic rows
is not asserted here.
-/

namespace LW56e2.Transport.Certificate
noncomputable section

theorem candidate_matches_endpoint :
    Candidate.p = Endpoint.perturbation ∧
    Candidate.B = Endpoint.boundary ∧
    Candidate.cushion = Endpoint.saving := by
  norm_num [Candidate.p, Candidate.B, Candidate.cushion, Geometry.boundary,
    Endpoint.perturbation, Endpoint.boundary, Endpoint.saving]

theorem adaptive_count_bounds {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    1 - δ ≤ Endpoint.adaptiveCount δ x ∧ Endpoint.adaptiveCount δ x ≤ 1 := by
  have hJ := Endpoint.countDenominator_pos hdlo hdhi hxlo hxhi
  have hd : 0 ≤ δ := by linarith
  have ha : 0 ≤ (5 / 6 : ℝ) - δ := by linarith
  have hP : 0 ≤ ((2 : ℝ) - 8 * x / 9) * (1 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hP2 : ((2 : ℝ) - 8 * x / 9) * (1 - x) ≤ 2 := by
    calc
      _ ≤ 2 * (1 - x) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 2 := by linarith
  have hD : (2 : ℝ) ≤ 3 - 17 * x / 9 := by linarith
  have hPD : ((2 : ℝ) - 8 * x / 9) * (1 - x) ≤ 3 - 17 * x / 9 :=
    hP2.trans hD
  have hPJ : (5 / 6 - δ) * ((2 - 8 * x / 9) * (1 - x)) ≤
      Endpoint.countDenominator δ x := by
    have hm := mul_le_mul_of_nonneg_left hPD ha
    have hn := mul_nonneg hd hP
    unfold Endpoint.countDenominator
    linarith
  have hnum : 0 ≤ (5 / 6 - δ) * δ * ((2 - 8 * x / 9) * (1 - x)) :=
    mul_nonneg (mul_nonneg ha hd) hP
  have hquot0 := div_nonneg hnum (show 0 ≤ 2 * Endpoint.countDenominator δ x by positivity)
  have hquot : (5 / 6 - δ) * δ * ((2 - 8 * x / 9) * (1 - x)) /
      (2 * Endpoint.countDenominator δ x) ≤ δ := by
    apply (div_le_iff₀ (show 0 < 2 * Endpoint.countDenominator δ x by positivity)).2
    have hm := mul_le_mul_of_nonneg_left hPJ hd
    have hn := mul_nonneg hd hJ.le
    nlinarith
  unfold Endpoint.adaptiveCount
  constructor <;> linarith

def rowSlope (δ x : ℝ) : ℝ := Endpoint.adaptiveCount δ x + δ / 2 - 17 / 50

theorem row_slope_bounds {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    0 ≤ rowSlope δ x ∧ rowSlope δ x ≤ 2 := by
  obtain ⟨hlo, hhi⟩ := adaptive_count_bounds hdlo hdhi hxlo hxhi
  unfold rowSlope
  constructor <;> linarith

def highExponent (d δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - Candidate.B + Geometry.h Candidate.p * (17 / 50 - 1 / 6) -
    ((1 + δ) / 2) * Geometry.ly Candidate.p - Geometry.ell Candidate.p / 2 +
    δ * x * Geometry.ell Candidate.p + d * rowSlope δ x

theorem high_exponent_endpoint (d δ x : ℝ) :
    highExponent d δ x = Endpoint.endpointExponent δ x +
      (d - Geometry.h Candidate.p) * rowSlope δ x := by
  unfold highExponent Endpoint.endpointExponent rowSlope
  unfold Candidate.B Candidate.p Geometry.boundary Geometry.h Geometry.ly Geometry.ell
  simp only [Endpoint.boundary, Endpoint.h, Endpoint.ly, Endpoint.ell, Endpoint.perturbation]
  ring

/-- Continuous, buffered row-scale bound for the specified high exponent. -/
theorem buffered_high_bound {d δ x : ℝ}
    (hd : d ≤ Geometry.h Candidate.p + Candidate.zeta)
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    highExponent d δ x ≤ -(3 / 160000000000 : ℝ) := by
  have he := Endpoint.adaptive_endpoint_bound hdlo hdhi hxlo hxhi
  obtain ⟨hs0, hs2⟩ := row_slope_bounds hdlo hdhi hxlo hxhi
  have hm := mul_le_mul_of_nonneg_right
    (show d - Geometry.h Candidate.p ≤ Candidate.zeta by linarith) hs0
  have hz := mul_le_mul_of_nonneg_left hs2 Candidate.zeta_pos.le
  rw [high_exponent_endpoint]
  norm_num [Candidate.zeta] at hm hz
  linarith

end
end LW56e2.Transport.Certificate
