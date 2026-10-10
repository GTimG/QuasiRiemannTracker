import WeightedQRH.NumeratorRamifiedMass
import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralSelected

/-! Coefficient masses for the original unramified correction and error. -/
noncomputable section
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeEuler ProbeLocal

structure CubicCoefficients where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
def CubicCoefficients.eval (c : CubicCoefficients) (T : ℂ) : ℂ :=
  cubic c.a c.b c.c c.d T
def CubicCoefficients.mass (c : CubicCoefficients) (r : ℝ) : ℝ :=
  cubicMass c.a c.b c.c c.d r

def unramifiedE₀ (Q : ℝ) (A eta v x z : ℂ) : ℂ :=
  markedDefectConstant (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹ (coordD Q eta v x)
def unramifiedE₁ (Q : ℝ) (A eta v x z : ℂ) : ℂ :=
  markedDefectLinear (coordR Q A x z) (coordV Q z) v
    (eta * (Q - 1) * (Q : ℂ) ^ (-x))

theorem coordK_split (Q : ℝ) (eta x w : ℂ) (hQ : 0 < Q) :
    coordK Q eta x w = (eta * (Q - 1) * (Q : ℂ) ^ (-x)) * (Q : ℂ) ^ (-w) := by
  unfold coordK
  rw [show -x - w = -x + -w by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne')]
  ring

theorem unramified_marked_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0) :
    unramifiedMarked Q A eta v x w z =
      affine (unramifiedE₀ Q A eta v x z) (unramifiedE₁ Q A eta v x z)
        ((Q : ℂ) ^ (-w)) - coordD Q eta v x := by
  have hh := marked_defect_affine (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordD Q eta v x) v (eta * (Q - 1) * (Q : ℂ) ^ (-x))
    ((Q : ℂ) ^ (-w)) hR hV
  unfold unramifiedMarked
  rw [coordK_split Q eta x w hQ]
  change markedFactor _ _ _ _ (-coordD Q eta v x + v * (Q : ℂ) ^ (-w) * _) 1 = _
  exact eq_sub_of_add_eq hh

def unramifiedDefectCoefficients (Q : ℝ) (A eta v x z : ℂ) : QuadraticCoefficients :=
  let V := coordV Q z
  let D := coordD Q eta v x
  let E₀ := unramifiedE₀ Q A eta v x z
  let E₁ := unramifiedE₁ Q A eta v x z
  ⟨correctionDefectConstant V D E₀, correctionDefectLinear V D v E₀ E₁,
    correctionDefectQuadratic V D v E₁⟩

theorem unramified_defect_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0)
    (hD : 1 - coordD Q eta v x ≠ 0) :
    unramifiedClosed Q A eta v x w z - 1 =
      (unramifiedDefectCoefficients Q A eta v x z).eval ((Q : ℂ) ^ (-w)) := by
  change continuedCorrection (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) - 1 = _
  rw [unramified_marked_expansion Q A eta v x w z hQ hR hV]
  exact correction_defect_quadratic _ _ _ _ _ _ hD

def unramifiedErrorCoefficients (Q : ℝ) (A eta v x z : ℂ) : CubicCoefficients :=
  let V := coordV Q z
  let D := coordD Q eta v x
  let B := star eta * (Q : ℂ) ^ x
  let nu := star v
  let E₀ := unramifiedE₀ Q A eta v x z
  let E₁ := unramifiedE₁ Q A eta v x z
  let c := (1 - V) / (1 - D)
  let a := errorBracketConstant V D B nu E₀
  let b := errorBracketLinear V D B nu E₀ E₁
  let d := errorBracketQuadratic E₁
  ⟨c * a, c * (b - v * a), c * (d - v * b), -c * v * d⟩

theorem unramified_error_expansion (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 0 < Q) (hR : 1 - coordR Q A x z ≠ 0) (hV : 1 - coordV Q z ≠ 0)
    (hD : 1 - coordD Q eta v x ≠ 0) (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1) :
    unramifiedSelected Q A eta v x w z + unramifiedClosed Q A eta v x w z * star v =
      (unramifiedErrorCoefficients Q A eta v x z).eval ((Q : ℂ) ^ (-w)) := by
  have hi := selected_phase_identities Q eta v x w hQ heta hv
  change compensatedReplacement (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta * (Q : ℂ) ^ x) ((Q : ℂ) ^ (-w)) +
    continuedCorrection (coordV Q z) (coordW Q v w) (coordD Q eta v x)
      (unramifiedMarked Q A eta v x w z) * star v = _
  rw [unramified_marked_expansion Q A eta v x w z hQ hR hV]
  exact compensated_error_cubic _ _ _ _ _ _ _ _ hV hD hi.1
    (PrincipalSlotEstimate.unit_phase_inverse v hv)

theorem unramified_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re) :
    1 - coordR Q A x z ≠ 0 ∧ 1 - coordV Q z ≠ 0 ∧ 1 - coordD Q eta v x ≠ 0 := by
  refine ⟨one_sub_ne_zero_of_norm_le_half _
    ((coordR_norm_le Q (by linarith) A x z hA).trans
      (rpow_le_half Q _ hQ (by linarith))),
    one_sub_ne_zero_of_norm_le_half _ (first_region_V_half Q hQ z hz), ?_⟩
  apply one_sub_ne_zero_of_norm_le_half
  exact (coordD_norm_le Q (by linarith) eta v x heta hv).trans
    (rpow_le_half Q _ hQ (by linarith))

/-- Summable unramified correction defect coefficient mass. -/
theorem unramified_defect_coefficient_mass (Q sigma eps : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (heps : 0 < eps) (hx : (51 / 100 : ℝ) ≤ x.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) (hsigma : -(1 / 100 : ℝ) ≤ sigma)
    (hxw : 1 + eps ≤ x.re + sigma) :
    (unramifiedDefectCoefficients Q A eta v x z).mass (Q ^ (-sigma)) ≤
      720 * Q ^ (-1 - min eps (1 / 50 : ℝ)) := by
  obtain ⟨hR,hV,hD⟩ := unramified_denominators Q A eta v x z hQ hA heta hv hx hz
  let c := unramifiedDefectCoefficients Q A eta v x z
  have hb := quadraticMass_le_of_vertical_bound Q sigma sigma
    (240 * Q ^ (-1 - min eps (1 / 50 : ℝ))) c.a c.b c.c (by linarith) le_rfl (by
      intro w hw
      have hh := unramifiedClosed_first_region_bound Q A eta v x w z eps
        hQ hA heta hv heps hx hz (by rw [hw]; exact hsigma) (by rw [hw]; exact hxw)
      rw [unramified_defect_expansion Q A eta v x w z (by linarith) hR hV hD] at hh
      exact hh)
  change quadraticMass c.a c.b c.c _ ≤ _
  nlinarith

/-- Actual unramified error coefficient mass, valid on both new reconstruction
lines.  Its prime exponent is strictly below −1/2. -/
theorem unramified_error_coefficient_mass (Q alpha eps sigma : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hsigma : 1 - alpha - 6 * eps ≤ sigma) :
    (unramifiedErrorCoefficients Q A eta v x z).mass (Q ^ (-sigma)) ≤
      2880 * Q ^ (-(51 / 100 : ℝ)) := by
  obtain ⟨hR,hV,hD⟩ := unramified_denominators Q A eta v x z hQ hA heta.le hv.le
    (by rw [hx]; linarith) (by rw [hz])
  let c := unramifiedErrorCoefficients Q A eta v x z
  have hb := cubicMass_le_of_vertical_bound Q (1 - alpha - 6 * eps) sigma
    (720 * Q ^ (-(51 / 100 : ℝ))) c.a c.b c.c c.d (by linarith) hsigma (by
      intro w hw
      have hh := unramifiedSelected_central_error Q alpha eps A eta v x w z
        hQ halpha halpha1 heps heps1 hA heta hv hx hw hz
      rw [unramified_error_expansion Q A eta v x w z (by linarith) hR hV hD heta hv] at hh
      exact hh)
  change cubicMass c.a c.b c.c c.d _ ≤ _
  nlinarith

end WeightedQRH.Numerator
