/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates
noncomputable section
set_option autoImplicit false

def intercept (q y : ℝ) : ℝ := (1+q)/(6*q*y)
def slope (y : ℝ) : ℝ := 1/y
def denominator (q k : ℝ) : ℝ := 6*q^2*k
def crossingNumerator (q y k : ℝ) : ℝ := q*(1+q)*k-y

/-- Exact slope derivative in reciprocal source coordinates. -/
theorem hasDerivAt_slope {y : ℝ → ℝ} {q k : ℝ}
    (hy : HasDerivAt y (-k) q) (hy0 : y q ≠ 0) :
    HasDerivAt (fun x => slope (y x)) (k/(y q)^2) q := by
  change HasDerivAt ((fun _ : ℝ => (1:ℝ)) / y) (k/(y q)^2) q
  simpa using (hasDerivAt_const q (1:ℝ)).div hy hy0

/-- Exact intercept derivative; the curve has decreasing coordinate q. -/
theorem hasDerivAt_intercept {y : ℝ → ℝ} {q k : ℝ}
    (hy : HasDerivAt y (-k) q) (hq : q ≠ 0) (hy0 : y q ≠ 0) :
    HasDerivAt (fun x => intercept x (y x))
      (crossingNumerator q (y q) k/(6*q^2*(y q)^2)) q := by
  have hd := ((hasDerivAt_id q).const_add 1).div
    (((hasDerivAt_id q).const_mul 6).mul hy) (by exact mul_ne_zero (mul_ne_zero (by norm_num) hq) hy0)
  convert hd using 1
  · unfold intercept
    rfl
  · dsimp [crossingNumerator]
    field_simp
    <;> ring

/-- The tangent crossing is the ratio of the actual source derivatives. -/
theorem tangent_ratio {q y k : ℝ} (hq : q ≠ 0) (hy : y ≠ 0) (hk : k ≠ 0) :
    (crossingNumerator q y k/(6*q^2*y^2))/(k/y^2) =
      crossingNumerator q y k/denominator q k := by
  unfold denominator
  field_simp

/-- The plain budget at the tangent crossing has a particularly simple form. -/
theorem tangent_budget {q y k : ℝ} (hq : q ≠ 0) (hy : y ≠ 0) (hk : k ≠ 0) :
    intercept q y - slope y*(crossingNumerator q y k/denominator q k) =
      1/denominator q k := by
  unfold intercept slope crossingNumerator denominator
  field_simp
  <;> ring

/-- Ratios of finite source differences tend to the tangent crossing. -/
theorem tendsto_secant_ratio {f g : ℝ → ℝ} {q df dg : ℝ}
    (hf : HasDerivAt f df q) (hg : HasDerivAt g dg q) (hdg : dg ≠ 0) :
    Filter.Tendsto (fun x => (f x-f q)/(g x-g q)) (nhdsWithin q {q}ᶜ)
      (nhds (df/dg)) := by
  have h := hf.tendsto_slope.div hg.tendsto_slope hdg
  convert h using 1
  funext x
  change (f x-f q)/(g x-g q) = _root_.slope f q x / _root_.slope g q x
  rw [slope_def_field, slope_def_field]
  by_cases hx : x=q
  · simp [hx]
  · field_simp [sub_ne_zero.mpr hx]

/-- The actual intercept/slope secant converges to S/D. -/
theorem tendsto_source_secant {y : ℝ → ℝ} {q k : ℝ}
    (hy : HasDerivAt y (-k) q) (hq : q ≠ 0) (hy0 : y q ≠ 0) (hk : k ≠ 0) :
    Filter.Tendsto (fun x => (intercept x (y x)-intercept q (y q))/
      (slope (y x)-slope (y q))) (nhdsWithin q {q}ᶜ)
      (nhds (crossingNumerator q (y q) k/denominator q k)) := by
  have h := tendsto_secant_ratio (hasDerivAt_intercept hy hq hy0)
    (hasDerivAt_slope hy hy0) (div_ne_zero hk (pow_ne_zero _ hy0))
  simpa only [tangent_ratio hq hy0 hk] using h

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveCoordinates.hasDerivAt_intercept
