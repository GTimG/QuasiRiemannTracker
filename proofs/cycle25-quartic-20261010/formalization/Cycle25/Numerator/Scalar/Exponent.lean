/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
import Cycle25.Assembly.Parameters
import Cycle25.Assembly.HighData
import Cycle25.Assembly.Count.Endpoint
import Cycle25.Arithmetic.Perturbation

noncomputable section
namespace Cycle25.Numerator.Scalar

theorem countingCoefficient_binding {kap p : ℝ} (hk : 7/10 ≤ kap) :
    OAI.SevenEighths.Cycle25DetectorRowCount.coefficient p kap = Arithmetic.countingCoefficient kap p := by
  rw [Arithmetic.canonical_counting_formula hk]
  unfold OAI.SevenEighths.Cycle25DetectorRowCount.coefficient
    OAI.SevenEighths.Cycle25DetectorRowCount.primeWeight
    OAI.SevenEighths.Cycle25DetectorRowCount.denominator
    OAI.SevenEighths.Cycle25DetectorRowCount.b
  ring

theorem rowCount_binding {kap p : ℝ} (hk : 7/10 ≤ kap) (delta : ℝ) :
    OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap = Arithmetic.rowExponent kap delta p := by
  unfold OAI.SevenEighths.Cycle25DetectorRowCount.rowCount Arithmetic.rowExponent Arithmetic.rowDen
  rw [countingCoefficient_binding hk]
  rfl

def numeratorExponent (kap d delta p : ℝ) : ℝ :=
  -ly/2+ell*(17/50-1/2)+delta*p*ell+
    d*((3*OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap+1)/4-17/50)-
      delta*p*(2*ly-d)/(12*kap)

def weightedSourceSZExponent (a e : ℝ) : ℝ :=
  lx*(1/2-17/50)+a+16*e+17/50-1

theorem numerator_kernel_exponent {kap : ℝ} (hk : 7/10 ≤ kap)
    (delta p e : ℝ) :
    numeratorExponent kap h delta p+weightedSourceSZExponent ((1+delta)/2) e =
      Arithmetic.fullBoundary kap delta p-(4+b)/6+16*e := by
  unfold numeratorExponent weightedSourceSZExponent Arithmetic.fullBoundary
  rw [rowCount_binding hk]
  simp only [b, lx, ly, ell, h, Arithmetic.x0, Arithmetic.y0]
  ring

theorem rowCount_bounds {kap delta p : ℝ} (hk : 7/10 ≤ kap)
    (hd : 0 ≤ delta ∧ delta ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    1-delta ≤ OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap ∧ OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap ≤ 1 := by
  rw [rowCount_binding hk]
  have hC := Arithmetic.countingCoefficient_pos hk hp
  have hDen := Arithmetic.rowDen_pos hk ⟨hd.1,by linarith [hd.2]⟩ hp
  have hV : 0 ≤ (5/6:ℝ)-delta := by linarith [hd.2]
  have hC1 : Arithmetic.countingCoefficient kap p ≤ 1 := by
    have hD : 0 < Arithmetic.countingDen kap p := by
      linarith [Arithmetic.countingDen_lower hk hp]
    apply (div_le_iff₀ hD).2
    unfold Arithmetic.countingDen
    have hm := mul_nonneg (show 0 ≤ kap by linarith) hp.1
    nlinarith [sq_nonneg p]
  have hCV : Arithmetic.countingCoefficient kap p*((5/6:ℝ)-delta) ≤
      Arithmetic.rowDen kap delta p := by
    have hm := mul_le_mul_of_nonneg_right hC1 hV
    unfold Arithmetic.rowDen
    nlinarith [mul_nonneg hd.1 hC.le]
  have hr : delta*Arithmetic.countingCoefficient kap p*((5/6:ℝ)-delta)/
      (2*Arithmetic.rowDen kap delta p) ≤ delta/2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hCV hd.1]
  unfold Arithmetic.rowExponent
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (mul_nonneg hd.1 hC.le) hV) (by positivity))
  · linarith

/-- The physical dyad extension shrinks with the contradiction gap. -/
theorem numerator_geometric_extension {kap d delta p t : ℝ} (hk : 7/10 ≤ kap)
    (_hd : 1/2 ≤ d) (_hd1 : d ≤ 1) (ht : 0 ≤ t) (htop : d ≤ h+3*t)
    (hdelta : 0 ≤ delta ∧ delta ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    numeratorExponent kap d delta p ≤ numeratorExponent kap h delta p+6*t := by
  have hr := rowCount_bounds hk hdelta hp
  have hR0 : 0 ≤ OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap := by linarith [hdelta.2]
  have hqp : 0 ≤ delta*p := mul_nonneg hdelta.1 hp.1
  have hqp1 : delta*p ≤ 3/8 := by
    have hm := mul_le_mul hdelta.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hm
    exact hm
  have hk0 : 0 < 12*kap := by linarith
  let slope := (3*OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta p kap+1)/4-17/50+
      delta*p/(12*kap)
  have hfrac0 : 0 ≤ delta*p/(12*kap) := by positivity
  have hfrac1 : delta*p/(12*kap) ≤ 1 := by
    apply (div_le_iff₀ hk0).2
    nlinarith
  have hs0 : 0 ≤ slope := by dsimp only [slope]; linarith [hdelta.2]
  have hs1 : slope ≤ 2 := by dsimp only [slope]; linarith [hr.2]
  have hid : numeratorExponent kap d delta p-numeratorExponent kap h delta p =
      (d-h)*slope := by
    unfold numeratorExponent
    dsimp only [slope]
    field_simp [ne_of_gt (show 0 < kap by linarith)]
    ring
  have hm := mul_le_mul_of_nonneg_right (show d-h ≤ 3*t by linarith) hs0
  have hm1 := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 3*t by positivity)
  linarith

theorem numerator_supremum_improvement {beta d delta p t : ℝ}
    (hbeta : theta < beta) (hd : 1/2 ≤ d) (hd1 : d ≤ 1)
    (ht : 0 ≤ t) (htop : d ≤ h+3*t)
    (hdelta : 0 ≤ delta ∧ delta ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    numeratorExponent (2*beta-1) d delta p+
      weightedSourceSZExponent ((1+delta)/2) 0 ≤
      signal beta-(4/5)*(beta-theta)+6*t := by
  have hk : (7:ℝ)/10 ≤ 2*beta-1 := by
    have hb0 := Arithmetic.kappa0_range.1
    rw [Arithmetic.kappa0_eq] at hb0
    change Arithmetic.b0 < beta at hbeta
    linarith
  have hext := numerator_geometric_extension hk hd hd1 ht htop hdelta hp
  have hb := Arithmetic.supremum_improvement hbeta
    ⟨hdelta.1,by linarith [hdelta.2]⟩ hp
  have hid := numerator_kernel_exponent hk delta p 0
  unfold signal theta at *
  linarith

end Cycle25.Numerator.Scalar
