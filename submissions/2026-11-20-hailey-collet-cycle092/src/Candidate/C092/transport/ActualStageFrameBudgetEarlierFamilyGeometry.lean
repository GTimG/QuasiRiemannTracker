/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine both-long reference companion fits the physical common
rectangle. No ordered Box for that companion is used. -/
import Candidate.C092.transport.ActualStageFrameBudgetEarlierFamilyIntake
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentEnergyBands
open QRH.Cycle090 QRH.Cycle092.NativeStrip QRH.Cycle092.ReferenceShortP3
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.OrderedPairPhase
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalWindow

/-- The common rectangle and its short reference follow from the actual
original X-arm ordered bounds and the both-long branch alone. -/
theorem earlier_reference_bounds (Z n y X₁ X₂:ℝ)(hZ:1<Z)
    (hy:y ≤ sourceY)(hn:n ≤ sourceRatio*y)
    (hX₁:0<X₁)(hX₂:0<X₂)
    (hxn:length Z X₁ ≤ n)(hxy:length Z X₂ ≤ y)
    (hlong₁:Z^shortWidth < X₁)(hlong₂:Z^shortWidth < X₂) :
    let q:=Z^shortWidth
    let Y₂:=X₁*X₂/q
    0<q ∧ 0<Y₂ ∧ X₁ ≤ Z ∧ X₂ ≤ Z ∧ q ≤ Z ∧ Y₂ ≤ Z ∧ q ≤ Y₂ ∧
      X₁*X₂=q*Y₂ ∧ max X₁ q ≤ Z ∧ max X₂ Y₂ ≤ Z := by
  intro q Y₂
  have hz:0<Z:=zero_lt_one.trans hZ
  have hN1:n ≤ 1:=by norm_num [sourceRatio,sourceY] at hn hy;linarith
  have hY1:y ≤ 1:=by norm_num [sourceY] at hy;linarith
  have hNY:n+y ≤ 1+shortWidth:=by
    norm_num [sourceRatio,sourceY,shortWidth] at hn hy ⊢;linarith
  have hxcap:X₁ ≤ Z:=by
    simpa only [Real.rpow_one] using (scale_le_of_length hZ hxn).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hN1)
  have hycap:X₂ ≤ Z:=by
    simpa only [Real.rpow_one] using (scale_le_of_length hZ hxy).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hY1)
  have hq:0<q:=Real.rpow_pos_of_pos hz _
  have hqcap:q ≤ Z:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le
      (show shortWidth ≤ (1:ℝ) by norm_num [shortWidth])
  have hprodCap:X₁*X₂ ≤ Z^(n+y):=by
    calc
      _ ≤ Z^n*Z^y:=mul_le_mul (scale_le_of_length hZ hxn) (scale_le_of_length hZ hxy)
        hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(n+y):=(Real.rpow_add hz _ _).symm
  have hY₂cap:Y₂ ≤ Z:=by
    calc
      _ ≤ Z^(n+y)/Z^shortWidth:=div_le_div_of_nonneg_right hprodCap hq.le
      _=Z^(n+y-shortWidth):=(Real.rpow_sub hz _ _).symm
      _ ≤ Z:=by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ.le
          (by linarith : n+y-shortWidth ≤ 1)
  have hqY₂:q ≤ Y₂:=by
    apply (le_div_iff₀ hq).mpr
    exact mul_le_mul hlong₁.le hlong₂.le hq.le hX₁.le
  refine ⟨hq,div_pos (mul_pos hX₁ hX₂) hq,hxcap,hycap,hqcap,hY₂cap,hqY₂,?_,
    max_le hxcap hqcap,max_le hycap hY₂cap⟩
  exact (mul_div_cancel₀ (X₁*X₂) hq.ne').symm.trans (by ring)

#print axioms earlier_reference_bounds
end
end QRH.Cycle092.ActualStageFrameBudget
