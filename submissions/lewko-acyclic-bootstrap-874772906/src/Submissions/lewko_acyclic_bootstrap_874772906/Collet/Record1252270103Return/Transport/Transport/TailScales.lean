/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.Bounds]
open scoped BigOperators
namespace SevenEighths.Record1252270103Return.TransportHighRowFamily
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
    (hlength : ∑i,length i=(Record1252270103Return.Transport.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(Record1252270103Return.Transport.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(Record1252270103Return.Transport.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+Record1252270103Return.Transport.Transport.b)/6-(Record1252270103Return.Transport.Arithmetic.y/2-Record1252270103Return.Transport.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Record1252270103Return.Transport.Assembly.row_endpoint, Record1252270103Return.Transport.Transport.b]
  linarith [Record1252270103Return.Transport.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Record1252270103Return.Transport.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(Record1252270103Return.Transport.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(Record1252270103Return.Transport.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+Record1252270103Return.Transport.Arithmetic.x/2+Record1252270103Return.Transport.Arithmetic.y)+(Record1252270103Return.Transport.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Record1252270103Return.Transport.Assembly.row_endpoint]
  ring

end SevenEighths.Record1252270103Return.TransportHighRowFamily
end

end OAI

#print axioms OAI.SevenEighths.Record1252270103Return.TransportHighRowFamily.selected_scale_power
#print axioms OAI.SevenEighths.Record1252270103Return.TransportHighRowFamily.physical_scale_power
#print axioms OAI.SevenEighths.Record1252270103Return.TransportHighRowFamily.small_source_scale
#print axioms OAI.SevenEighths.Record1252270103Return.TransportHighRowFamily.large_source_scale
