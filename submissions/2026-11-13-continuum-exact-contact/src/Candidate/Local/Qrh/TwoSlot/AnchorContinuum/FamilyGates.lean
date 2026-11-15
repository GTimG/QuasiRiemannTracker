/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ReserveGate

/-! Uniform stage gates for the strict source curve, including the retained
source-pad debit and all HIGH classes. No finite numerical table is used. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Set Qrh.TwoSlot.AnchorExtension.ChainData
open Qrh.TwoSlot.AnchorZeroLoss.High

theorem stageDatum_r {R : ℝ} (hR : R ≠ 0) (z v k r q : ℝ) :
    (stageDatum R z v k (r/R) q).r = r := by
  exact div_mul_cancel₀ r hR

theorem stageDatum_s {R : ℝ} (hR : R ≠ 0) (z v k r q : ℝ) :
    (stageDatum R z v k (r/R) q).s = fs R z k r := by
  have hc := div_mul_cancel₀ r hR
  unfold Stg.s Stg.u stageDatum fs fS fY fu
  dsimp
  linear_combination -(1/2:ℝ)*hc

theorem stageDatum_u (R z v k r q : ℝ) :
    (stageDatum R z v k (r/R) q).u = fu R r := rfl

theorem datum_high_gates {R z v k r q gamma : ℝ}
    (hR : R ∈ Icc (3/4:ℝ) (7/9)) (hr : r ∈ Icc (3/4:ℝ) R)
    (hz : z ∈ Icc (0:ℝ) (11/10000)) (hv : v ∈ Icc (-4/45:ℝ) 0)
    (hk : 45457/125000 ≤ k ∧ k < 1/2) (hg : 0 < gamma)
    (hq : 0 < q) (hqu : q ≤ 1/1000000000000) (hqg : q ≤ gamma/1000)
    (hcut : k*(2+6*(z-R*v+R*gamma)) = 1)
    (hreserve : 3*gamma ≤ v-Curve.flow R z) (hstep : R-r ≤ 1/10000) :
    ∀ p ∈ classes k, ∃ w ∈ cutoffs, R+q ≤ w ∧
      w+Tolerances.sig q (z-R*v-q/5) (-v) w ≤ 6 ∧
      Tolerances.detEx q (z-R*v-q/5) (-v) p.1 p.2 w r (fs R z k r) (fH R r) ≤ fu R r := by
  have hR0 : 0 < R := by linarith [hR.1]
  have hH : r/R ∈ Icc (9/10:ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ hR0]
      linarith [hr.1,hR.2]
    · exact (div_le_one hR0).mpr hr.2
  have hF := reserve_gate hR hk.1 hv.1 hH.1 hg hq hqg hcut hreserve
  have ha : (stageDatum R z v k (r/R) q).a1 ∈ Icc (0:ℝ) (1/10) := by
    change -v ∈ Icc (0:ℝ) (1/10)
    constructor <;> linarith [hv.1,hv.2]
  have hgap : (stageDatum R z v k (r/R) q).z-(stageDatum R z v k (r/R) q).a0+
      (stageDatum R z v k (r/R) q).a1*(stageDatum R z v k (r/R) q).R ∈
        Icc (0:ℝ) (1/1000000) := by
    change z-(z-R*v-q/5)+(-v)*R ∈ Icc (0:ℝ) (1/1000000)
    constructor <;> nlinarith
  have hu := (step_u_bounds hR.1 hr.2 hstep).2
  have hHyp := structural_high_gates (d:=stageDatum R z v k (r/R) q)
    hR hH hz hk ha hgap hu hF
  have ha0 : (stageDatum R z v k (r/R) q).a0 ≤ 1 := by
    have hm := mul_le_mul hR.2 (show -v ≤ 4/45 by linarith [hv.1])
      (show 0 ≤ -v by linarith [hv.2]) (by norm_num : (0:ℝ) ≤ 7/9)
    change z-R*v-q/5 ≤ 1
    nlinarith [hz.2]
  have hall := HighGates.class_gates hHyp hq hqu hR.1 ha0
  simp only [stageDatum_r hR0.ne',stageDatum_s hR0.ne',stageDatum_u] at hall
  simpa only [stageDatum,fH] using hall

/-- Complete scalar inputs for every sufficiently short curve stage. -/
theorem curve_stage_gates {lam T gamma R r q : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hT : 3/4 ≤ T) (hT1 : T ≤ 7/9)
    (hR : R ∈ Icc (3/4:ℝ) T) (hr : r ∈ Icc (3/4:ℝ) R)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1/100)
    (hq : 0 < q) (hqu : q ≤ 1/1000000000000) (hqg : q ≤ gamma/1000)
    (hreserve : 3*gamma ≤ Curve.D lam T R-Curve.flow R (Curve.W lam T R))
    (hstep : R-r ≤ 1/10000) :
    Qrh.MarkedAnchor.Price.StageHyp R (Curve.W lam T R) (Curve.cut lam T gamma R) r ∧
    Qrh.TwoSlot.AnchorZeroLoss.High.tinyEx r
      (fs R (Curve.W lam T R) (Curve.cut lam T gamma R) r) (fH R r) ≤ fu R r-3/100 ∧
    ∀ p ∈ classes (Curve.cut lam T gamma R), ∃ w ∈ cutoffs, R+q ≤ w ∧
      w+Tolerances.sig q (Curve.W lam T R-R*Curve.D lam T R-q/5) (-Curve.D lam T R) w ≤ 6 ∧
      Tolerances.detEx q (Curve.W lam T R-R*Curve.D lam T R-q/5) (-Curve.D lam T R)
        p.1 p.2 w r (fs R (Curve.W lam T R) (Curve.cut lam T gamma R) r) (fH R r) ≤ fu R r := by
  obtain ⟨hcoarse,htiny⟩ := curve_coarse_gates hlam hlam1 hT hT1 hR hr hg hg1 hstep
  obtain ⟨hz0,hz1⟩ := Curve.W_bounds hlam hlam1 hT hT1 hR
  have hv := Curve.D_bounds hlam hlam1 hT hT1 hR
  have hk := Curve.cut_bounds hlam hlam1 hT hT1 hR hg hg1
  have hden : 0 < 2+6*(Curve.W lam T R-R*Curve.D lam T R+R*gamma) := by
    have hR0 : 0 < R := by linarith [hR.1]
    have hprod := mul_nonpos_of_nonneg_of_nonpos hR0.le hv.2
    have hpos := mul_pos hR0 hg
    linarith
  have hcut : Curve.cut lam T gamma R*
      (2+6*(Curve.W lam T R-R*Curve.D lam T R+R*gamma)) = 1 := by
    unfold Curve.cut
    exact div_mul_cancel₀ _ hden.ne'
  exact ⟨hcoarse,htiny,datum_high_gates ⟨hR.1,hR.2.trans hT1⟩ hr ⟨hz0,hz1.le⟩
    ⟨by linarith [hv.1],hv.2⟩ hk
    hg hq hqu hqg hcut hreserve hstep⟩

end
end Qrh.TwoSlot.AnchorContinuum
