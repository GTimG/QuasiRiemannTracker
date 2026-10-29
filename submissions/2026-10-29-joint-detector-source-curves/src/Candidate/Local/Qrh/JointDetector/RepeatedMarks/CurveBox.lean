/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurveBernstein

namespace Qrh.JointDetector.RepeatedMarks.CurveBernstein
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 60000
open scoped BigOperators
open BernsteinBox Set

theorem reconstruct35_interval (a : Fin 4 → Fin 6 → ℝ) (lo hi x y : ℝ) :
    powerEval a (lo+(hi-lo)*x) y = bernEval (coefficients a lo hi) x y := by
  norm_num [powerEval,bernEval,coefficients,intervalPower,Fin.sum_univ_succ,Nat.choose]
  ring

theorem rectangle_nonneg (a : Fin 4 → Fin 6 → ℝ) (xl xh yl yh x y : ℝ)
    (hxwidth : xl < xh) (hywidth : yl < yh)
    (hx : x ∈ Icc xl xh) (hy : y ∈ Icc yl yh)
    (hc : ∀ i j, 0 ≤ coefficients (widthShift a yl yh) xl xh i j) :
    0 ≤ powerEval a x y := by
  let ξ := (x-xl)/(xh-xl)
  let η := (y-yl)/(yh-yl)
  have hξ : ξ ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hxwidth).le,
      (div_le_one (sub_pos.mpr hxwidth)).2 (by linarith [hx.2])⟩
  have hη : η ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hy.1) (sub_pos.mpr hywidth).le,
      (div_le_one (sub_pos.mpr hywidth)).2 (by linarith [hy.2])⟩
  have hxeq : xl+(xh-xl)*ξ=x := by
    dsimp [ξ]
    field_simp [(sub_pos.mpr hxwidth).ne']
    linarith
  have hyeq : yl+(yh-yl)*η=y := by
    dsimp [η]
    field_simp [(sub_pos.mpr hywidth).ne']
    linarith
  have hp := bernEval_nonneg hc hξ hη
  rw [←reconstruct35_interval,widthShift_eval,hxeq,hyeq] at hp
  exact hp

/-- A finite rational subdivision certificate. Its constructors prove
coverage of the closed parent rectangle, including every shared boundary. -/
inductive BoxCertificate (a : Fin 4 → Fin 6 → ℝ) : ℝ → ℝ → ℝ → ℝ → Prop
  | leaf {xl xh yl yh : ℝ} : xl < xh → yl < yh →
      (∀ i j, 0 ≤ coefficients (widthShift a yl yh) xl xh i j) →
      BoxCertificate a xl xh yl yh
  | splitX {xl xh yl yh m : ℝ} :
      BoxCertificate a xl m yl yh → BoxCertificate a m xh yl yh →
      BoxCertificate a xl xh yl yh
  | splitY {xl xh yl yh m : ℝ} :
      BoxCertificate a xl xh yl m → BoxCertificate a xl xh m yh →
      BoxCertificate a xl xh yl yh

theorem BoxCertificate.nonneg {a : Fin 4 → Fin 6 → ℝ} {xl xh yl yh : ℝ}
    (h : BoxCertificate a xl xh yl yh) :
    ∀ x ∈ Icc xl xh, ∀ y ∈ Icc yl yh, 0 ≤ powerEval a x y := by
  induction h with
  | leaf hxw hyw hc =>
    intro x hx y hy
    exact rectangle_nonneg _ _ _ _ _ _ _ hxw hyw hx hy hc
  | @splitX xl xh yl yh m h1 h2 ih1 ih2 =>
    intro x hx y hy
    by_cases hm : x ≤ m
    · exact ih1 x ⟨hx.1,hm⟩ y hy
    · exact ih2 x ⟨by linarith,hx.2⟩ y hy
  | @splitY xl xh yl yh m h1 h2 ih1 ih2 =>
    intro x hx y hy
    by_cases hm : y ≤ m
    · exact ih1 x hx y ⟨hy.1,hm⟩
    · exact ih2 x hx y ⟨by linarith,hy.2⟩

/-- Transport a certified full curved region back to its physical density.
This uses the whole mapped triangle, including collapsed endpoints. -/
theorem curved_nonneg_of_certificate
    (a : Fin 4 → Fin 3 → ℝ) (k e0 ev hi vl vh ν v : ℝ)
    (hv : v ∈ Icc vl vh) (hE : 0 < e0+ev*v)
    (hνlo : k/(e0+ev*v) ≤ ν) (hνhi : ν ≤ hi)
    (hc : BoxCertificate (mapped a k e0 ev hi) 0 1 vl vh) :
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
  have hνeq : (k+(hi*E-k)*x)/E=ν := by
    rw [hrel]
    exact mul_div_cancel_left₀ _ hEp.ne'
  have hp := hc.nonneg x hx v hv
  rw [mapped_eval _ _ _ _ _ _ _ hE.ne'] at hp
  change 0 ≤ E^3*powerEval a ((k+(hi*E-k)*x)/E) v at hp
  rw [hνeq] at hp
  exact (mul_nonneg_iff_of_pos_left (pow_pos hEp 3)).1 hp

#print axioms BoxCertificate.nonneg
end
end Qrh.JointDetector.RepeatedMarks.CurveBernstein
