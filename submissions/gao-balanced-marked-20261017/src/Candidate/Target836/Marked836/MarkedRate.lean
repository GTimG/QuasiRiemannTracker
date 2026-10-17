import Candidate.Target836.Marked836.VariableSupply

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Marked836.VariableSupply
noncomputable section

def coefficient (d : ℝ) : ℝ := (32/39)*phi d

theorem phi_nonneg {d : ℝ} (hd0 : 13/20 ≤ d) (hd : d ≤ 7/10) :
    0 ≤ phi d := by
  unfold phi
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

theorem phi_le_one_fifth {d : ℝ} (hd0 : 13/20 ≤ d) (hd : d ≤ 7/10) :
    phi d ≤ 1/5 := by
  have hden : 0 < 5-2*d := by linarith
  have hprod := mul_nonneg (show 0 ≤ d-13/20 by linarith)
    (show 0 ≤ 6*d-3/2 by linarith)
  unfold phi
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem coefficient_nonneg {d : ℝ} (hd0 : 13/20 ≤ d) (hd : d ≤ 7/10) :
    0 ≤ coefficient d := by
  unfold coefficient
  exact mul_nonneg (by norm_num) (phi_nonneg hd0 hd)

theorem coefficient_le_delta {d : ℝ} (hd0 : 13/20 ≤ d) (hd : d ≤ 7/10) :
    coefficient d ≤ d := by
  have hp := phi_le_one_fifth hd0 hd
  unfold coefficient
  nlinarith

/-- A finite-difference lower bound sufficient to combine the changing marked
coefficient with the increasing HIGH reserve, without a derivative oracle. -/
theorem phi_lower_lipschitz {d e : ℝ}
    (hd0 : 13/20 ≤ d) (hd : d ≤ 7/10)
    (he0 : 13/20 ≤ e) (he : e ≤ 7/10) (hde : d ≤ e) :
    phi d-(e-d) ≤ phi e := by
  have hdd : 0 < 5-2*d := by linarith
  have hed : 0 < 5-2*e := by linarith
  have hprod : (13/20:ℝ)*(13/20) ≤ d*e :=
    mul_le_mul hd0 he0 (by norm_num) (by linarith)
  have hpoly : 0 ≤ 8*d*e-20*d-20*e+25 := by nlinarith
  have hnon := mul_nonneg (show 0 ≤ 2*(e-d) by linarith) hpoly
  have hid : (5-2*d)*(5-2*e)*(phi e-phi d+(e-d)) =
      2*(e-d)*(8*d*e-20*d-20*e+25) := by
    unfold phi
    field_simp
    <;> ring
  have hpos : 0 < (5-2*d)*(5-2*e) := mul_pos hdd hed
  have hh : 0 ≤ phi e-phi d+(e-d) :=
    (mul_nonneg_iff_of_pos_left hpos).mp (hid.symm ▸ hnon)
  linarith

/-- The original root cutoff/core and positive divisor-tail price already pay
the exact changing coefficient, throughout the larger lower-delta range. -/
theorem old_root_tail_dominates {d : ℝ}
    (hd0 : 13/20 ≤ d) (hd : d ≤ 7/10) :
    coefficient d*(13/400)*(122/125)+(121/3375000) ≤
      (6*density d-1-9/100)/250 := by
  have hden : 0 < 5-2*d := by linarith
  have hn := mul_nonneg (show 0 ≤ 7-10*d by linarith)
    (show 0 ≤ 11815-13176*d by linarith)
  have hid : (5-2*d)*((6*density d-1-9/100)/250-
      coefficient d*(13/400)*(122/125)-(121/3375000)) =
      (7-10*d)*(11815-13176*d)/843750 := by
    unfold coefficient phi density
    field_simp
    <;> ring
  have hright : 0 ≤ (7-10*d)*(11815-13176*d)/843750 :=
    div_nonneg hn (by norm_num)
  have hh : 0 ≤ (6*density d-1-9/100)/250-
      coefficient d*(13/400)*(122/125)-(121/3375000) :=
    (mul_nonneg_iff_of_pos_left hden).mp (hid.symm ▸ hright)
  linarith

end
end Marked836.VariableSupply

#print axioms Marked836.VariableSupply.phi_lower_lipschitz
#print axioms Marked836.VariableSupply.old_root_tail_dominates
