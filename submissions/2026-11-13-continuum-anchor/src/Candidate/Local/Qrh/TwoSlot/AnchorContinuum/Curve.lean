/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Calculus of the strict source subcurves used by the continuum construction.
These are real-calculus facts, not a marked-moment supplier by themselves. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum.Curve

def q0 (r : ℝ) : ℝ := (r^4*(r-2/3))^(1/5:ℝ)
def P (r : ℝ) : ℝ := 11*r/16-7/24
def A (r : ℝ) : ℝ := (4/5)/r+(1/5)/(r-2/3)
def b (r : ℝ) : ℝ := (3*r-7/3)/(r*(15*r-10))
def flow (r z : ℝ) : ℝ := A r*z+b r
def Z (T r : ℝ) : ℝ := P r-(P T/q0 T)*q0 r
def W (lam T r : ℝ) : ℝ := lam*Z T r
def D (lam T r : ℝ) : ℝ := lam*flow r (Z T r)

theorem q0_pos {r : ℝ} (hr : 2/3 < r) : 0 < q0 r := by
  unfold q0
  exact Real.rpow_pos_of_pos (mul_pos (pow_pos (by linarith) _) (by linarith)) _

theorem A_eq {r : ℝ} (hr : 2/3 < r) :
    A r = (15*r-8)/(r*(15*r-10)) := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hs : r-2/3 ≠ 0 := ne_of_gt (by linarith)
  have hl : 15*r-10 ≠ 0 := ne_of_gt (by linarith)
  have hn3 : -2+r*3 ≠ 0 := by linarith
  have hn15 : -10+r*15 ≠ 0 := by linarith
  unfold A
  ring_nf
  field_simp [hr0,hn3,hn15]
  <;> ring

theorem hasDerivAt_q0 {r : ℝ} (hr : 2/3 < r) :
    HasDerivAt q0 (A r*q0 r) r := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hs : r-2/3 ≠ 0 := ne_of_gt (by linarith)
  have hn3 : -2+r*3 ≠ 0 := by linarith
  have hp : 0 < r^4*(r-2/3) := mul_pos (pow_pos (by linarith) _) (by linarith)
  have hd := ((hasDerivAt_id r).pow 4).mul ((hasDerivAt_id r).sub_const (2/3))
  change HasDerivAt (fun x : ℝ => (x^4*(x-2/3))^(1/5:ℝ)) (A r*q0 r) r
  convert hd.rpow_const (p := (1/5:ℝ)) (Or.inl hp.ne') using 1
  · rfl
  · unfold A q0
    simp only [Pi.mul_apply,Pi.pow_apply,id_eq,mul_one]
    rw [Real.rpow_sub_one hp.ne']
    ring_nf
    field_simp [hr0,hn3]
    <;> ring

theorem hasDerivAt_P (r : ℝ) : HasDerivAt P (11/16) r := by
  convert ((hasDerivAt_id r).const_mul (11/16)).sub_const (7/24) using 1
  · funext x
    unfold P
    simp only [id_eq]
    ring
  · ring

theorem P_flow {r : ℝ} (hr : 2/3 < r) : 11/16 = flow r (P r) := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hl : 15*r-10 ≠ 0 := ne_of_gt (by linarith)
  unfold flow
  rw [A_eq hr]
  unfold P b
  field_simp [hr0,hl]
  <;> ring

theorem hasDerivAt_Z (T : ℝ) {r : ℝ} (hr : 2/3 < r) :
    HasDerivAt (Z T) (flow r (Z T r)) r := by
  change HasDerivAt (fun x => P x-(P T/q0 T)*q0 x) (flow r (Z T r)) r
  convert (hasDerivAt_P r).sub ((hasDerivAt_q0 hr).const_mul (P T/q0 T)) using 1
  rw [P_flow hr]
  unfold flow Z
  ring

theorem hasDerivAt_W (lam T : ℝ) {r : ℝ} (hr : 2/3 < r) :
    HasDerivAt (W lam T) (D lam T r) r :=
  (hasDerivAt_Z T hr).const_mul lam

theorem Z_seed {T : ℝ} (hT : 2/3 < T) : Z T T = 0 := by
  unfold Z
  rw [div_mul_cancel₀ _ (q0_pos hT).ne',sub_self]

theorem W_seed (lam : ℝ) {T : ℝ} (hT : 2/3 < T) : W lam T T = 0 := by
  simp only [W,Z_seed hT,mul_zero]

theorem strict_reserve_identity (lam T r : ℝ) :
    D lam T r-flow r (W lam T r) = (lam-1)*b r := by
  unfold D W flow
  ring

theorem forcing_neg {r : ℝ} (hr : 2/3 < r) (hr1 : r < 7/9) : b r < 0 := by
  unfold b
  exact div_neg_of_neg_of_pos (by linarith) (mul_pos (by linarith) (by linarith))

/-- Shrinking the seed solution creates a positive differential reserve at
 every point, including the seed, before any finite stage grid is chosen. -/
theorem strict_reserve_pos {lam T r : ℝ} (hlam : lam < 1)
    (hr : 2/3 < r) (hr1 : r < 7/9) :
    0 < D lam T r-flow r (W lam T r) := by
  rw [strict_reserve_identity]
  exact mul_pos_of_neg_of_neg (by linarith) (forcing_neg hr hr1)

end Qrh.TwoSlot.AnchorContinuum.Curve
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.hasDerivAt_Z
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.strict_reserve_pos
