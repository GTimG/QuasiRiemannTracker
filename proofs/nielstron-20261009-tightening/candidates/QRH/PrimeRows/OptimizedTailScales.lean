import QRH.NumericFacts
import OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import QRH.Geometry
import OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Actual physical tails at optimized scales. -/
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.QRHPhysicalTails
open ProbeHighRowFamily

section
variable {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
include K Z hZ length

lemma selected_scale_power (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  have hQRH := QRH.NumericFacts.h_lower
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  have hQRH := QRH.NumericFacts.h_lower
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  try simp only [QRH.C, QRH.h]
  ring

lemma small_source_scale
    (hlength : ∑i,length i=QRH.ell) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^QRH.lx)^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^QRH.ly)^((1/2:ℝ)-1))=Z^(QRH.C β-(QRH.ly/2-(13/75)*QRH.h)+8*e) := by
  have hQRH := QRH.NumericFacts.h_lower
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  try simp only [QRH.C, QRH.h]
  ring

end

lemma small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤Z) (hU : 1≤U)
    (hUsmall : U≤Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=QRH.ell) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^QRH.lx)^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^QRH.ly)^((1/2:ℝ)-1))≤Z^(QRH.C β-(QRH.ly/2-(13/75)*QRH.h-1/50)+8*e) := by
  have hQRH := QRH.NumericFacts.h_lower
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(QRH.C β-(QRH.ly/2-(13/75)*QRH.h)+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1;ring

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=QRH.ell) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^QRH.lx)^(1/2-b)*Z^(2+b-1)*(Z^QRH.ly)^((2:ℝ)-1))=
      Z^((1+QRH.lx/2+QRH.ly)+QRH.h*b) := by
  have hQRH := QRH.NumericFacts.h_lower
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  try simp only [QRH.C, QRH.h]
  ring

end SevenEighths.QRHPhysicalTails
end

end OAI
