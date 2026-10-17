import Candidate.Target830.Marked.VariableSupply

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Marked830.VariableSupply

theorem rescaled_exact_marked_power_padded
    (U Y d dmax pad delta q S loss : ℝ)
    (hU : 1 ≤ U) (hY : 0 < Y) (hd : 0 < d) (hdmax : d ≤ dmax)
    (hbase : U^d=Y*U^pad) (hloss : 0 ≤ loss) :
    (U^d)^(density delta+q*(S/d)-phi delta*chosenWidth delta (S/d)+loss) ≤
      U^(q*S-physicalGain delta S d+dmax*loss+pad*density delta)*Y^(density delta) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hYeq : Y=U^(d-pad) := by
    rw [Real.rpow_sub hUp]
    apply (eq_div_iff (Real.rpow_pos_of_pos hUp pad).ne').mpr
    exact hbase.symm
  have hgain := physicalGain_rescale delta S d hd
  have hexp : d*(density delta+q*(S/d)-phi delta*chosenWidth delta (S/d)+loss) =
      q*S-physicalGain delta S d+d*loss+d*density delta := by
    have hcancel : d*(S/d)=S := mul_div_cancel₀ _ hd.ne'
    linear_combination q*hcancel-hgain
  rw [←Real.rpow_mul hUp.le,hexp,hYeq,←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_right hdmax hloss
  linarith

end Marked830.VariableSupply
#print axioms Marked830.VariableSupply.rescaled_exact_marked_power_padded
