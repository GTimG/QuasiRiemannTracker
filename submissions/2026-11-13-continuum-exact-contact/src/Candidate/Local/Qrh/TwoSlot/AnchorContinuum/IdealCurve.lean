/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.FiniteCurve

/-! The ideal source is attained in the original open-rectangle contract.
Each requested decrement uses one finite strict-curve construction. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Set Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native

def ideal (r : ℝ) : ℝ := Curve.Z (7/9) r

theorem continuousAt_approximation (r : ℝ) :
    ContinuousAt (fun t : ℝ => Curve.W (1-t) (7/9-t) r) 0 := by
  have ht : ContinuousAt (fun t : ℝ => 7/9-t) 0 := continuousAt_const.sub continuousAt_id
  have hp : ContinuousAt (fun t : ℝ => Curve.P (7/9-t)) 0 := by
    unfold Curve.P
    fun_prop
  have hq : ContinuousAt (fun t : ℝ => Curve.q0 (7/9-t)) 0 :=
    (Curve.hasDerivAt_q0 (by norm_num : (2/3:ℝ) < 7/9-0)).continuousAt.comp ht
  have hqn : Curve.q0 (7/9-(0:ℝ)) ≠ 0 :=
    (Curve.q0_pos (by norm_num)).ne'
  unfold Curve.W Curve.Z
  exact (continuousAt_const.sub continuousAt_id).mul
    (continuousAt_const.sub ((hp.div hq hqn).mul continuousAt_const))

/-- A fixed positive reserve is paid by a finite legal curve. No analytic
constants are passed through this elementary approximation. -/
theorem exists_strict_approximation {r eps : ℝ} (hr : 3/4 ≤ r) (hr1 : r < 7/9)
    (heps : 0 < eps) :
    ∃ lam T : ℝ, 0 < lam ∧ lam < 1 ∧ 3/4 ≤ T ∧ T < 7/9 ∧ r ≤ T ∧
      ideal r-eps < Curve.W lam T r := by
  obtain ⟨eta,heta,hclose⟩ := Metric.continuousAt_iff.mp (continuousAt_approximation r) eps heps
  let rho : ℝ := min eta (min 1 (7/9-r))
  have hrho : 0 < rho := lt_min heta (lt_min (by norm_num) (by linarith))
  let t : ℝ := rho/2
  have ht : 0 < t := div_pos hrho (by norm_num)
  have hte : t < eta := by have := min_le_left eta (min 1 (7/9-r)); dsimp [t,rho]; linarith
  have ht1 : t < 1 := by
    have h := (min_le_right eta (min 1 (7/9-r))).trans (min_le_left _ _)
    dsimp [t,rho]
    linarith
  have htr : t < 7/9-r := by
    have h := (min_le_right eta (min 1 (7/9-r))).trans (min_le_right _ _)
    dsimp [t,rho]
    linarith
  have hdt : dist t (0:ℝ) < eta := by
    simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using hte
  have hd := hclose hdt
  have hab : |Curve.W (1-t) (7/9-t) r-ideal r| < eps := by
    simpa only [Real.dist_eq,sub_zero,Curve.W,one_mul,ideal] using hd
  refine ⟨1-t,7/9-t,by linarith,by linarith,by linarith,by linarith,by linarith,?_⟩
  linarith [(abs_lt.mp hab).1]

/-- The complete paired moment source on the ideal curve, with all positive
rectangle decrements and the actual physical coefficient contracts. -/
theorem ideal_anchor (F : ParentFace)
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource)
    (hparent : QRH.Record1252270103Source.GlobalSource F.B₀ F.L₀ F.c₀)
    {r : ℝ} (hr : 3/4 ≤ r) (hr1 : r < 7/9) : AnchorAt r (ideal r) := by
  intro delta hdelta
  obtain ⟨lam,T,hlam,hlam1,hT,hT1,hrT,happrox⟩ :=
    exists_strict_approximation hr hr1 (by positivity : 0 < delta/2)
  have hsource := strict_curve_anchor F hβ hres hparent hlam hlam1 hT hT1 r ⟨hr,hrT⟩
  exact hsource.rect (by positivity : 0 < delta/2)
    (anchorRect_restricts (by linarith) (by linarith))

/-- Exact polynomial identity for the ideal source. This removes real roots
from the rational affine-minorant certificate. -/
theorem ideal_gap_pow_five {r : ℝ} (hr : 2/3 < r) :
    (Curve.P r-ideal r)^5 = (5/16:ℝ)^5*7*r^4*(r-2/3) := by
  have hq := Curve.q0_pow_five hr
  have hqt := Curve.q0_pow_five (r := 7/9) (by norm_num)
  have hqn := (Curve.q0_pos (r := 7/9) (by norm_num)).ne'
  unfold ideal Curve.Z
  rw [sub_sub_cancel, mul_pow, div_pow, hq, hqt]
  norm_num [Curve.P] <;> ring

/-- A positive fifth-power comparison suffices to certify a source line.
The sign hypothesis prevents selecting a spurious algebraic branch. -/
theorem le_ideal_of_fifth_power {r a : ℝ} (hr : 2/3 < r)
    (ha : 0 ≤ Curve.P r-a)
    (hpow : (5/16:ℝ)^5*7*r^4*(r-2/3) ≤ (Curve.P r-a)^5) :
    a ≤ ideal r := by
  have hgap : 0 ≤ Curve.P r-ideal r := by
    unfold ideal Curve.Z
    have hp : 0 < Curve.P (7/9) := by norm_num [Curve.P]
    have hq := Curve.q0_pos hr
    have hqt := Curve.q0_pos (r := 7/9) (by norm_num)
    nlinarith [mul_pos (div_pos hp hqt) hq]
  rw [←ideal_gap_pow_five hr] at hpow
  have hle : Curve.P r-ideal r ≤ Curve.P r-a := by
    by_contra hn
    have hh : Curve.P r-a < Curve.P r-ideal r := lt_of_not_ge hn
    have := pow_lt_pow_left₀ hh ha (by norm_num : (5:ℕ) ≠ 0)
    linarith
  linarith

end
end Qrh.TwoSlot.AnchorContinuum
