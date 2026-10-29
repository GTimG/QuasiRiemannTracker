/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.BernsteinBox

namespace Qrh.JointDetector.RepeatedMarks.CurveBernstein
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 60000
open scoped BigOperators
open BernsteinBox Set

/-- Clear a cubic density denominator after mapping the full curved region
q(v) ≤ ν ≤ hi to a rectangle. All density/width cross terms are retained. -/
def mapped (a : Fin 4 → Fin 3 → ℝ) (k e0 ev hi : ℝ)
    (h : Fin 4) (l : Fin 6) : ℝ :=
  ![![a 0 0*e0^3 + a 1 0*k*e0^2 + a 2 0*k^2*e0 + a 3 0*k^3,
      (3:ℝ)*a 0 0*e0^2*ev + a 0 1*e0^3 + (2:ℝ)*a 1 0*k*e0*ev + a 1 1*k*e0^2 + a 2 0*k^2*ev + a 2 1*k^2*e0 + a 3 1*k^3,
      (3:ℝ)*a 0 0*e0*ev^2 + (3:ℝ)*a 0 1*e0^2*ev + a 0 2*e0^3 + a 1 0*k*ev^2 + (2:ℝ)*a 1 1*k*e0*ev + a 1 2*k*e0^2 + a 2 1*k^2*ev + a 2 2*k^2*e0 + a 3 2*k^3,
      a 0 0*ev^3 + (3:ℝ)*a 0 1*e0*ev^2 + (3:ℝ)*a 0 2*e0^2*ev + a 1 1*k*ev^2 + (2:ℝ)*a 1 2*k*e0*ev + a 2 2*k^2*ev,
      a 0 1*ev^3 + (3:ℝ)*a 0 2*e0*ev^2 + a 1 2*k*ev^2,
      a 0 2*ev^3],
    ![a 1 0*(hi*e0-k)*e0^2 + (2:ℝ)*a 2 0*k*(hi*e0-k)*e0 + (3:ℝ)*a 3 0*k^2*(hi*e0-k),
      (2:ℝ)*a 1 0*(hi*e0-k)*e0*ev + a 1 0*(hi*ev)*e0^2 + a 1 1*(hi*e0-k)*e0^2 + (2:ℝ)*a 2 0*k*(hi*e0-k)*ev + (2:ℝ)*a 2 0*k*(hi*ev)*e0 + (2:ℝ)*a 2 1*k*(hi*e0-k)*e0 + (3:ℝ)*a 3 0*k^2*(hi*ev) + (3:ℝ)*a 3 1*k^2*(hi*e0-k),
      a 1 0*(hi*e0-k)*ev^2 + (2:ℝ)*a 1 0*(hi*ev)*e0*ev + (2:ℝ)*a 1 1*(hi*e0-k)*e0*ev + a 1 1*(hi*ev)*e0^2 + a 1 2*(hi*e0-k)*e0^2 + (2:ℝ)*a 2 0*k*(hi*ev)*ev + (2:ℝ)*a 2 1*k*(hi*e0-k)*ev + (2:ℝ)*a 2 1*k*(hi*ev)*e0 + (2:ℝ)*a 2 2*k*(hi*e0-k)*e0 + (3:ℝ)*a 3 1*k^2*(hi*ev) + (3:ℝ)*a 3 2*k^2*(hi*e0-k),
      a 1 0*(hi*ev)*ev^2 + a 1 1*(hi*e0-k)*ev^2 + (2:ℝ)*a 1 1*(hi*ev)*e0*ev + (2:ℝ)*a 1 2*(hi*e0-k)*e0*ev + a 1 2*(hi*ev)*e0^2 + (2:ℝ)*a 2 1*k*(hi*ev)*ev + (2:ℝ)*a 2 2*k*(hi*e0-k)*ev + (2:ℝ)*a 2 2*k*(hi*ev)*e0 + (3:ℝ)*a 3 2*k^2*(hi*ev),
      a 1 1*(hi*ev)*ev^2 + a 1 2*(hi*e0-k)*ev^2 + (2:ℝ)*a 1 2*(hi*ev)*e0*ev + (2:ℝ)*a 2 2*k*(hi*ev)*ev,
      a 1 2*(hi*ev)*ev^2],
    ![a 2 0*(hi*e0-k)^2*e0 + (3:ℝ)*a 3 0*k*(hi*e0-k)^2,
      a 2 0*(hi*e0-k)^2*ev + (2:ℝ)*a 2 0*(hi*e0-k)*(hi*ev)*e0 + a 2 1*(hi*e0-k)^2*e0 + (6:ℝ)*a 3 0*k*(hi*e0-k)*(hi*ev) + (3:ℝ)*a 3 1*k*(hi*e0-k)^2,
      (2:ℝ)*a 2 0*(hi*e0-k)*(hi*ev)*ev + a 2 0*(hi*ev)^2*e0 + a 2 1*(hi*e0-k)^2*ev + (2:ℝ)*a 2 1*(hi*e0-k)*(hi*ev)*e0 + a 2 2*(hi*e0-k)^2*e0 + (3:ℝ)*a 3 0*k*(hi*ev)^2 + (6:ℝ)*a 3 1*k*(hi*e0-k)*(hi*ev) + (3:ℝ)*a 3 2*k*(hi*e0-k)^2,
      a 2 0*(hi*ev)^2*ev + (2:ℝ)*a 2 1*(hi*e0-k)*(hi*ev)*ev + a 2 1*(hi*ev)^2*e0 + a 2 2*(hi*e0-k)^2*ev + (2:ℝ)*a 2 2*(hi*e0-k)*(hi*ev)*e0 + (3:ℝ)*a 3 1*k*(hi*ev)^2 + (6:ℝ)*a 3 2*k*(hi*e0-k)*(hi*ev),
      a 2 1*(hi*ev)^2*ev + (2:ℝ)*a 2 2*(hi*e0-k)*(hi*ev)*ev + a 2 2*(hi*ev)^2*e0 + (3:ℝ)*a 3 2*k*(hi*ev)^2,
      a 2 2*(hi*ev)^2*ev],
    ![a 3 0*(hi*e0-k)^3,
      (3:ℝ)*a 3 0*(hi*e0-k)^2*(hi*ev) + a 3 1*(hi*e0-k)^3,
      (3:ℝ)*a 3 0*(hi*e0-k)*(hi*ev)^2 + (3:ℝ)*a 3 1*(hi*e0-k)^2*(hi*ev) + a 3 2*(hi*e0-k)^3,
      a 3 0*(hi*ev)^3 + (3:ℝ)*a 3 1*(hi*e0-k)*(hi*ev)^2 + (3:ℝ)*a 3 2*(hi*e0-k)^2*(hi*ev),
      a 3 1*(hi*ev)^3 + (3:ℝ)*a 3 2*(hi*e0-k)*(hi*ev)^2,
      a 3 2*(hi*ev)^3]] h l

def widthShift (a : Fin 4 → Fin 6 → ℝ) (lo hi : ℝ)
    (i : Fin 4) (j : Fin 6) : ℝ :=
  ∑ l : Fin 6, if j.val ≤ l.val then
    a i l*((l.val.choose j.val:ℕ):ℝ)*lo^(l.val-j.val)*(hi-lo)^j.val else 0

theorem mapped_eval (a : Fin 4 → Fin 3 → ℝ) (k e0 ev hi x v : ℝ)
    (hE : e0+ev*v ≠ 0) :
    powerEval (mapped a k e0 ev hi) x v =
      (e0+ev*v)^3*powerEval a ((k+(hi*(e0+ev*v)-k)*x)/(e0+ev*v)) v := by
  norm_num [powerEval,mapped,Fin.sum_univ_succ,Nat.choose]
  field_simp
  <;> ring

theorem widthShift_eval (a : Fin 4 → Fin 6 → ℝ) (lo hi x y : ℝ) :
    powerEval (widthShift a lo hi) x y = powerEval a x (lo+(hi-lo)*y) := by
  norm_num [powerEval,widthShift,Fin.sum_univ_succ,Nat.choose]
  ring

theorem reconstruct35 (a : Fin 4 → Fin 6 → ℝ) (x y : ℝ) :
    powerEval a x y = bernEval (coefficients a 0 1) x y := by
  norm_num [powerEval,bernEval,coefficients,intervalPower,Fin.sum_univ_succ,Nat.choose]
  ring

/-- Endpoint collapse of a curved cell is permitted. No density monotonicity
is assumed, and the entire curved triangle is represented. -/
theorem curved_nonneg (a : Fin 4 → Fin 3 → ℝ) (k e0 ev hi vl vh ν v : ℝ)
    (hwidth : vl < vh) (hv : v ∈ Icc vl vh) (hE : 0 < e0+ev*v)
    (hνlo : k/(e0+ev*v) ≤ ν) (hνhi : ν ≤ hi)
    (hc : ∀ i j, 0 ≤ coefficients (widthShift (mapped a k e0 ev hi) vl vh) 0 1 i j) :
    0 ≤ powerEval a ν v := by
  let E := e0+ev*v
  have hEp : 0 < E := hE
  have hk : k ≤ E*ν := by
    have hh := (div_le_iff₀ hEp).1 hνlo
    nlinarith only [hh]
  have hhi : E*ν ≤ hi*E := by nlinarith [mul_le_mul_of_nonneg_left hνhi hEp.le]
  have hd : 0 ≤ hi*E-k := by linarith
  obtain ⟨x,hx,hrel⟩ : ∃ x ∈ Icc (0:ℝ) 1, k+(hi*E-k)*x=E*ν := by
    by_cases he : hi*E-k=0
    · refine ⟨0,⟨le_rfl,zero_le_one⟩,?_⟩
      nlinarith only [hk,hhi,he]
    · have hdp : 0 < hi*E-k := lt_of_le_of_ne hd (Ne.symm he)
      refine ⟨(E*ν-k)/(hi*E-k),⟨div_nonneg (by linarith) hdp.le,
        (div_le_one hdp).2 (by linarith)⟩,?_⟩
      field_simp
      <;> ring
  let y := (v-vl)/(vh-vl)
  have hy : y ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hv.1) (sub_pos.mpr hwidth).le
    · exact (div_le_one (sub_pos.mpr hwidth)).2 (by linarith [hv.2])
  have hveq : vl+(vh-vl)*y=v := by
    dsimp [y]
    field_simp [(sub_pos.mpr hwidth).ne']
    linarith
  have hνeq : (k+(hi*E-k)*x)/E=ν := by
    rw [hrel]
    exact mul_div_cancel_left₀ _ hEp.ne'
  have hpos := bernEval_nonneg hc hx hy
  rw [←reconstruct35, widthShift_eval, hveq, mapped_eval _ _ _ _ _ _ _ hE.ne'] at hpos
  change 0 ≤ E^3*powerEval a ((k+(hi*E-k)*x)/E) v at hpos
  rw [hνeq] at hpos
  exact (mul_nonneg_iff_of_pos_left (pow_pos hEp 3)).1 hpos

end
end Qrh.JointDetector.RepeatedMarks.CurveBernstein
