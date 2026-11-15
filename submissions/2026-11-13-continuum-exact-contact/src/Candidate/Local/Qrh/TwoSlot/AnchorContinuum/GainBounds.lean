/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Uniform gain bounds for all strict continuum subcurves. The algebraic endpoint
comparison uses exact fifth powers, not decimal approximations. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.SlopeBounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum.Curve
open Set

def coefficient (T : ℝ) : ℝ := P T/q0 T

theorem hasDerivAt_coefficient {r : ℝ} (hr : 2/3 < r) :
    HasDerivAt coefficient (b r/q0 r) r := by
  have hq := (q0_pos hr).ne'
  convert (hasDerivAt_P r).div (hasDerivAt_q0 hr) hq using 1
  · rfl
  · rw [P_flow hr]
    unfold flow
    field_simp [hq]
    <;> ring

theorem antitoneOn_coefficient : AntitoneOn coefficient (Icc (3/4:ℝ) (7/9)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
  · intro r hr
    exact (hasDerivAt_coefficient (by linarith [hr.1])).continuousAt.continuousWithinAt
  · intro r hr
    have hh := interior_subset hr
    exact (hasDerivAt_coefficient (by linarith [hh.1])).hasDerivWithinAt
  · intro r hr
    have hh := interior_subset hr
    exact div_nonpos_of_nonpos_of_nonneg
      (forcing_nonpos (by linarith [hh.1]) hh.2) (q0_pos (by linarith [hh.1])).le

theorem Z_le_limit {T r : ℝ} (hT : T ∈ Icc (3/4:ℝ) (7/9)) (hr : 2/3 < r) :
    Z T r ≤ Z (7/9) r := by
  have hc := antitoneOn_coefficient hT ⟨by norm_num,le_rfl⟩ hT.2
  have hm := mul_le_mul_of_nonneg_right hc (q0_pos hr).le
  unfold coefficient at hm
  unfold Z
  linarith

theorem q0_pow_five {r : ℝ} (hr : 2/3 < r) : (q0 r)^5 = r^4*(r-2/3) := by
  have hp : 0 ≤ r^4*(r-2/3) := (mul_pos (pow_pos (by linarith) _) (by linarith)).le
  unfold q0
  rw [←Real.rpow_natCast,←Real.rpow_mul hp]
  norm_num

theorem limit_gain_small : Z (7/9) (3/4) < (11/10000:ℝ) := by
  let d := (P (7/9)/q0 (7/9))*q0 (3/4)
  have hqT : 0 < q0 (7/9) := q0_pos (by norm_num)
  have hqa : 0 < q0 (3/4) := q0_pos (by norm_num)
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact (mul_pos (div_pos (by norm_num [P]) hqT) hqa).le
  have hd5 : d^5 = (P (7/9))^5/((7/9:ℝ)^4*(7/9-2/3))*
      ((3/4:ℝ)^4*(3/4-2/3)) := by
    dsimp [d]
    rw [mul_pow,div_pow,q0_pow_five (r := 7/9) (by norm_num),
      q0_pow_five (r := 3/4) (by norm_num)]
  have hpow : (P (3/4)-11/10000)^5 < d^5 := by
    rw [hd5]
    norm_num [P]
  have hlt : P (3/4)-11/10000 < d := by
    by_contra hh
    have hh' : d ≤ P (3/4)-11/10000 := le_of_not_gt hh
    have hle := pow_le_pow_left₀ hd0 hh' 5
    exact (not_le_of_gt hpow) hle
  change P (3/4)-d < 11/10000
  linarith

/-- The complete uniform gain range used by the limiting stage gates. -/
theorem W_bounds {lam T r : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hT : 3/4 ≤ T) (hT1 : T ≤ 7/9) (hr : r ∈ Icc (3/4:ℝ) T) :
    0 ≤ W lam T r ∧ W lam T r < 11/10000 := by
  have hz : 0 ≤ Z T r := by
    simpa only [W,one_mul] using W_nonneg (lam := 1) (by norm_num) hT hT1 hr
  have hscale : W lam T r ≤ Z T r := by
    simpa only [W,one_mul] using mul_le_mul_of_nonneg_right hlam1 hz
  have hlim := Z_le_limit ⟨hT,hT1⟩ (show 2/3 < r by linarith [hr.1])
  have ha := antitoneOn_W (lam := 1) (T := 7/9) (by norm_num) (by norm_num) le_rfl
    ⟨le_rfl,by norm_num⟩ ⟨hr.1,hr.2.trans hT1⟩ hr.1
  have ha' : Z (7/9) r ≤ Z (7/9) (3/4) := by simpa only [W,one_mul] using ha
  exact ⟨W_nonneg hlam hT hT1 hr,hscale.trans_lt (hlim.trans_lt (ha'.trans_lt limit_gain_small))⟩

end Qrh.TwoSlot.AnchorContinuum.Curve
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.W_bounds
