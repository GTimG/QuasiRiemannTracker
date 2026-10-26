import Candidate.Cycle63.Marked.DeletionFiniteExceptions
import Candidate.Cycle63.Marked.DeletionMaxAmplitude

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- Conductor padding has exactly the additional density cost pad*ρ;
normalization retains the full physical amplitude and width saving. -/
theorem rescaled_marked_power_padded (U Y d d₀ dmax pad ρ δ S loss : ℝ) (G : ℝ → ℝ → ℝ)
    (hU : 1≤ U) (hY : 0< Y) (hd : 0< d) (hdmax : d≤ dmax)
    (hbase : U^d=Y*U^pad) (hloss : 0≤ loss)
    (hscale : d*G (S/d) 1 = G S d) (hmono : G S d₀ ≤ G S d) :
    (U^d)^(ρ+δ*(S/d)-G (S/d) 1+loss) ≤
      U^(δ*S-G S d₀+dmax*loss+pad*ρ)*Y^ρ := by
  have hUp : 0< U := zero_lt_one.trans_le hU
  have hcore : (U^d)^ρ=Y^ρ*U^(pad*ρ) := by
    rw [hbase,Real.mul_rpow hY.le (Real.rpow_nonneg hUp.le _),←Real.rpow_mul hUp.le]
  calc
    _ ≤ U^(δ*S-G S d₀+dmax*loss)*(U^d)^ρ := by
      rw [←Real.rpow_mul hUp.le,←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
      apply Real.rpow_le_rpow_of_exponent_le hU
      have he : d*(δ*(S/d))=δ*S := by field_simp
      have heq : d*(ρ+δ*(S/d)-G (S/d) 1+loss)=d*ρ+δ*S-d*G (S/d) 1+d*loss := by rw [←he];ring
      rw [heq,hscale]
      nlinarith [mul_le_mul_of_nonneg_right hdmax hloss]
    _ = _ := by rw [hcore];simp only [Real.rpow_add hUp];ring

end
end OAI.SevenEighths.Deletion26
