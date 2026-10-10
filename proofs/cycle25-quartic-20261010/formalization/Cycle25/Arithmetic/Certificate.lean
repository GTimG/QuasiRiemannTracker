import Cycle25.Arithmetic.AlgebraicForms

/-! The exact polynomial certificate from B0.49. All coefficient identities are
verified in Lean, using the algebraic root relation, rather than numerical sampling. -/

namespace Cycle25.Arithmetic

noncomputable def certT : ℝ := ell0-(h0-4*ell0)/(12*kappa0)
noncomputable def certk0 : ℝ := b0-(1+ell0)/2-h0/3
noncomputable def certk1 : ℝ := -1/2+3*h0/4-certT/2
noncomputable def certK : ℝ := 8*(24-216*kappa0)*certk1+18*h0*(24*kappa0-4)
noncomputable def certA10 : ℝ := 8*(120*kappa0+80)*certk0
noncomputable def certA11 : ℝ :=
  8*((300*kappa0-40)*certT+(120*kappa0+80)*certk1+(144*kappa0-96)*certk0)-15*h0*(48*kappa0)
noncomputable def certA12 : ℝ := 8*((24-216*kappa0)*certT+(144*kappa0-96)*certk1)+18*h0*(48*kappa0)
noncomputable def certA20 : ℝ := 8*((120*kappa0+80)*certT+96*certk0)-15*h0*16
noncomputable def certA21 : ℝ := 8*((144*kappa0-96)*certT+96*certk1)+18*h0*16

noncomputable def certTPoly : ℝ := (-107020651/284324837) + (10777515509/5686496740) * ell0 + (4792397229/568649674) * ell0^2 + (-27460249389/5686496740) * ell0^3
noncomputable def certKPoly : ℝ := (68512621584/284324837) + (-622826635656/1421624185) * ell0 + (122316868800/284324837) * ell0^2 + (-181484567064/1421624185) * ell0^3
noncomputable def certA10Poly : ℝ := (87728742200/284324837) + (-535522104160/284324837) * ell0 + (451803856200/284324837) * ell0^2 + (-114989084640/284324837) * ell0^3
noncomputable def certA11Poly : ℝ := (-61885021440/284324837) + (372585555024/284324837) * ell0 + (-1940825802960/284324837) * ell0^2 + (946378571616/284324837) * ell0^3
noncomputable def certA12Poly : ℝ := (705445344/2516149) + (-2207857008/12580745) * ell0 + (9465572448/2516149) * ell0^2 + (-24316485552/12580745) * ell0^3
noncomputable def certA20Poly : ℝ := (-82067841600/284324837) + (272874521856/284324837) * ell0 + (1865417596320/284324837) * ell0^2 + (-1021092398496/284324837) * ell0^3
noncomputable def certA21Poly : ℝ := (153518482944/284324837) + (317929676448/1421624185) * ell0 + (-3548627116416/284324837) * ell0^2 + (8857647944352/1421624185) * ell0^3

theorem certT_poly : certT = certTPoly := by
  have hk : 12*kappa0 ≠ 0 := ne_of_gt (by linarith [kappa0_range.1])
  have hid : h0-4*ell0 = (ell0-certTPoly)*(12*kappa0) := by
    rw [h0_poly]
    simp only [hPoly, certTPoly, kappa0]
    have hp := ell0_quartic
    unfold quartic at hp
    linear_combination (-((-88868121/2843248370)))*hp
  have hq : (h0-4*ell0)/(12*kappa0) = ell0-certTPoly := (div_eq_iff hk).2 hid
  simp only [certT]
  rw [hq]
  ring

theorem certK_poly : certK = certKPoly := by
  simp only [certK, certk1]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certKPoly, kappa0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((3775160196/1421624185))*hp

theorem certA10_poly : certA10 = certA10Poly := by
  simp only [certA10, certk0]
  rw [h0_poly]
  simp only [hPoly, certA10Poly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((42659840/284324837))*hp

theorem certA11_poly : certA11 = certA11Poly := by
  simp only [certA11, certk0, certk1]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certA11Poly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((1473081744/284324837))*hp

theorem certA12_poly : certA12 = certA12Poly := by
  simp only [certA12, certk1]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certA12Poly, kappa0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((-9683155296/1421624185))*hp

theorem certA20_poly : certA20 = certA20Poly := by
  simp only [certA20, certk0]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certA20Poly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((710944968/284324837))*hp

theorem certA21_poly : certA21 = certA21Poly := by
  simp only [certA21, certk1]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certA21Poly, kappa0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((4265669808/1421624185))*hp

set_option maxHeartbeats 1000000 in
theorem tangency_constant : 8*(300*kappa0-40)*certk0 = certK*delta0^2 := by
  rw [certK_poly, delta0_poly]
  simp only [certk0]
  rw [h0_poly]
  simp only [certKPoly, deltaPoly, hPoly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((-535841160673310/458293822040679) + (160341946084451/152764607346893) * ell0 + (-43840582925935/305529214693786) * ell0^2 + (-795280181869641/1527646073468930) * ell0^3 + (175627044476289/1527646073468930) * ell0^4 + (114494076246501/1527646073468930) * ell0^5)*hp

set_option maxHeartbeats 1000000 in
theorem tangency_linear : 8*((300*kappa0-40)*certk1+(24-216*kappa0)*certk0)-15*h0*(24*kappa0-4) = -2*certK*delta0 := by
  rw [certK_poly, delta0_poly]
  simp only [certk0, certk1]
  rw [h0_poly, certT_poly]
  simp only [certKPoly, deltaPoly, hPoly, certTPoly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((-707020991482/208410105521) + (-163660339476/1042050527605) * ell0 + (-211731994908/1042050527605) * ell0^2)*hp

private theorem ell0_power_bounds (n : ℕ) : rootLo^n ≤ ell0^n ∧ ell0^n ≤ rootHi^n := by
  have hlo : 0 ≤ rootLo := by norm_num [rootLo]
  have he : 0 ≤ ell0 := by linarith [ell0_coarse.1]
  exact ⟨pow_le_pow_left₀ hlo (le_of_lt ell0_lo) n,
    pow_le_pow_left₀ he (le_of_lt ell0_hi) n⟩

theorem coefficient_minorants :
    36 < certA10 ∧ -174 < certA11 ∧ 347 < certA12 ∧
    38 < certA20 ∧ 257 < certA21 ∧ 179 < certK ∧ certK < 180 ∧
    117 < 768*certT ∧ 768*certT < 119 := by
  have he := ell0_lo
  have he' := ell0_hi
  have he2 := ell0_power_bounds 2
  have he3 := ell0_power_bounds 3
  norm_num [rootLo, rootHi] at he he' he2 he3
  rw [certA10_poly, certA11_poly, certA12_poly, certA20_poly, certA21_poly, certK_poly, certT_poly]
  simp only [certA10Poly, certA11Poly, certA12Poly, certA20Poly, certA21Poly, certKPoly, certTPoly]
  repeat' constructor
  all_goals linarith

end Cycle25.Arithmetic
