import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A symbolic barrier for the current QRH exponent model.
This concerns the existing parameter relations and counting estimate, not the
possibility of improving nonvanishing by a different analytic argument. -/
namespace QRH.MethodBarrier

noncomputable section

def theta (e : ℝ) : ℝ := 11 / 12 - e / 4
def height (e b : ℝ) : ℝ := (1 + 3 * e + b) / 2
def longLength (e b : ℝ) : ℝ := (1 - e + b) / 2
def c (e : ℝ) : ℝ := 2 / (5 - 3 * e)
def D (e x : ℝ) : ℝ := 3 - (1 + 2 * c e) * x
def P (e x : ℝ) : ℝ := (2 - 2 * c e * x) * (1 - x)
def J (e δ x : ℝ) : ℝ := (5 / 6 - δ) * D e x + δ * P e x

def F (e b δ y : ℝ) : ℝ :=
  -J e δ (1 / 2 - y) * ((1 + δ) / 2 - theta e - height e b / 6 -
    (1 + δ) / 2 * longLength e b - e / 2 + (1 / 2 - y) * δ * e +
    height e b * (1 - δ / 2)) -
    height e b * (5 / 6 - δ) * δ * P e (1 / 2 - y) / 2

def deltaStar (e : ℝ) : ℝ := (5 - 9 * e) / (6 * (3 * e + 1))
def cubic (e : ℝ) : ℝ := 657 * e ^ 3 - 954 * e ^ 2 + 21 * e + 20

/-- At this endpoint witness, the shape parameter `b` only affects the positive
height factor. Optimizing `b` cannot change the sign of the cubic obstruction. -/
theorem endpoint_identity (e b : ℝ) (ha : 3 * e + 1 ≠ 0) (hb : 5 - 3 * e ≠ 0) :
    F e b (deltaStar e) 0 =
      height e b * cubic e / (12 * (3 * e + 1) ^ 2 * (5 - 3 * e)) := by
  have hab : (3 * e + 1) ^ 2 * (5 - 3 * e) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ha) hb
  have ha2 : (3 * e + 1) ^ 2 ≠ 0 := pow_ne_zero _ ha
  ring_nf at ha hb hab ha2
  unfold F J D P c theta height longLength deltaStar cubic
  field_simp [ha, hb, hab, ha2]
  ring_nf
  field_simp [ha, hb, hab, ha2]
  <;> ring

/-- The obstruction witness belongs to the rectangle used by the certificate. -/
theorem deltaStar_range (e : ℝ) (he0 : (1 / 6 : ℝ) ≤ e) (he1 : e ≤ 1 / 5) :
    (1 / 3 : ℝ) ≤ deltaStar e ∧ deltaStar e ≤ 5 / 6 := by
  have hd : 0 < 6 * (3 * e + 1) := by linarith
  unfold deltaStar
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_le_iff₀ hd).mpr
    linarith

/-- A positive certificate at this point requires positivity of the cubic.
This is a necessary condition on this certificate model, not on all proofs. -/
theorem cubic_pos_of_endpoint_pos (e b : ℝ)
    (he0 : (1 / 6 : ℝ) ≤ e) (he1 : e ≤ 1 / 5)
    (hh : 0 < height e b) (hF : 0 < F e b (deltaStar e) 0) : 0 < cubic e := by
  have ha : 0 < 3 * e + 1 := by linarith
  have hb : 0 < 5 - 3 * e := by linarith
  rw [endpoint_identity e b ha.ne' hb.ne'] at hF
  by_contra hn
  have hp : cubic e ≤ 0 := le_of_not_gt hn
  have hnum : height e b * cubic e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh.le hp
  have hden : 0 ≤ 12 * (3 * e + 1) ^ 2 * (5 - 3 * e) := by positivity
  exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg hnum hden)) hF

end
end QRH.MethodBarrier

#print axioms QRH.MethodBarrier.endpoint_identity
#print axioms QRH.MethodBarrier.deltaStar_range
#print axioms QRH.MethodBarrier.cubic_pos_of_endpoint_pos
