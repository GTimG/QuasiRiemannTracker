import OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.WeightedHighRowFamily
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
    (hlength : ∑i,length i=(167/1000:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(747/2000:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(919/2000:ℝ))^((1/2:ℝ)-1))=Z^(β-681/1000-9221/100000+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(167/1000:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(747/2000:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(919/2000:ℝ))^((2:ℝ)-1))=
      Z^((1317/800:ℝ)+(1587/2000:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

end SevenEighths.WeightedHighRowFamily
end

end OAI
