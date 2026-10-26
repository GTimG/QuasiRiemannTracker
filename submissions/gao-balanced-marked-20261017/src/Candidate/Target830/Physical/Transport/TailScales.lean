/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
import Candidate.Target830.Physical.ProbeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Target830PhysicalHighRowFamily
open ProbeHighRowFamily

lemma selected_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ) (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Target830Physical.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(Target830Physical.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(Target830Physical.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+Target830Physical.Transport.b)/6-(Target830Physical.Arithmetic.y/2-Target830Physical.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Target830Physical.Assembly.row_endpoint, Target830Physical.Transport.b]
  linarith [Target830Physical.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Target830Physical.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(Target830Physical.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(Target830Physical.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+Target830Physical.Arithmetic.x/2+Target830Physical.Arithmetic.y)+(Target830Physical.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Target830Physical.Assembly.row_endpoint]
  ring

end SevenEighths.Target830PhysicalHighRowFamily
end

end OAI

#print axioms OAI.SevenEighths.Target830PhysicalHighRowFamily.selected_scale_power
#print axioms OAI.SevenEighths.Target830PhysicalHighRowFamily.physical_scale_power
#print axioms OAI.SevenEighths.Target830PhysicalHighRowFamily.small_source_scale
#print axioms OAI.SevenEighths.Target830PhysicalHighRowFamily.large_source_scale
