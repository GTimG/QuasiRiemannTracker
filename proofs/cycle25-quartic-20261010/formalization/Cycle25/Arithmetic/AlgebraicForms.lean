import Cycle25.Arithmetic.Geometry

/-! Polynomial representatives of the endpoint parameters in Q[ell0]/(quartic).
Every representative below is verified by ordinary ring arithmetic using ell0_quartic.
The rational computations that suggested these expressions are not proof oracles. -/

namespace Cycle25.Arithmetic

noncomputable def deltaPoly : ℝ := (4255/4398) + (-9075/2932) * ell0 + (823/1466) * ell0^2 + (2163/2932) * ell0^3
noncomputable def countPoly : ℝ := (661/2907) + (61/204) * ell0 + (7655/1938) * ell0^2 + (-2575/1292) * ell0^3
noncomputable def rprimePoly : ℝ := (-270599/136800) + (35413/7200) * ell0 + (342793/45600) * ell0^2 + (-72203/15200) * ell0^3
noncomputable def hPoly : ℝ := (181525300/284324837) + (393539385/284324837) * ell0 + (-813066675/284324837) * ell0^2 + (247160448/284324837) * ell0^3

theorem delta0_poly : delta0 = deltaPoly := by
  unfold delta0
  apply (div_eq_iff (ne_of_gt delta0_den_pos)).2
  have hp := ell0_quartic
  unfold quartic at hp
  unfold deltaPoly
  linear_combination ((59+21*ell0)/1466)*hp

theorem count0_poly : count0 = countPoly := by
  unfold count0
  apply (div_eq_iff (ne_of_gt count0_den_pos)).2
  have hp := ell0_quartic
  unfold quartic at hp
  unfold countPoly kappa0
  linear_combination (-125/7752)*hp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem rprime0_poly : rprime0 = rprimePoly := by
  have hp := ell0_quartic
  unfold quartic at hp
  have hid : count0*(v0^2-delta0^2*count0) =
      (rprimePoly+1)*(2*(v0+delta0*count0)^2) := by
    unfold v0
    rw [delta0_poly, count0_poly]
    unfold deltaPoly countPoly rprimePoly
    linear_combination (-((-1850156447833/6189830479823616) + (88781606967431189/11925740057793500160) * ell0 + (601208208889333027/4969058357413958400) * ell0^2 + (-798255385330938761/79504933718623334400) * ell0^3 + (-124580769109824421/174352924821542400) * ell0^4 + (16293028907208269/87176462410771200) * ell0^5 + (543818563504917311/414088196451163200) * ell0^6 + (-3875935381540667357/4416940762145740800) * ell0^7 + (-21318954494550061/73615679369095680) * ell0^8 + (2649881780969587/9815423915879424) * ell0^9 + (306384259895/21525052447104) * ell0^10 + (-96650255286725/4362410629279744) * ell0^11))*hp
  have hq : count0*(v0^2-delta0^2*count0)/(2*(v0+delta0*count0)^2) = rprimePoly+1 :=
    (div_eq_iff (ne_of_gt rprime0_den_pos)).2 hid
  unfold rprime0
  rw [hq]
  ring

theorem h0_poly : h0 = hPoly := by
  have hk : kappa0 ≠ 0 := ne_of_gt (lt_trans (by norm_num) kappa0_range.1)
  have hh : hPoly*(18*kappa0*rprime0-1)+12*kappa0*(1+ell0)+4*ell0 = 0 := by
    rw [rprime0_poly]
    unfold hPoly rprimePoly kappa0
    have hp := ell0_quartic
    unfold quartic at hp
    linear_combination ((248456502563/2593042513440) + (530749913/22745986960) * ell0 + (-546973817511/4321737522400) * ell0^2 + (5414358564/135054297575) * ell0^3)*hp
  unfold h0
  apply (div_eq_iff (ne_of_lt h0_den_neg)).2
  apply mul_right_cancel₀ (show 24*kappa0 ≠ 0 by exact mul_ne_zero (by norm_num) hk)
  have hn : -((1+ell0)/2+ell0/(6*kappa0))*(24*kappa0) =
      -12*kappa0*(1+ell0)-4*ell0 := by field_simp; ring
  have hd : (3*rprime0/4-1/(24*kappa0))*(24*kappa0) = 18*kappa0*rprime0-1 := by
    field_simp; ring
  rw [hn]
  rw [mul_assoc hPoly, hd]
  linear_combination -hh

end Cycle25.Arithmetic
