/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
namespace OAI

noncomputable section
variable [QRH.RH20261023Return.Geometry.Parameters] [QRH.RH20261023Return.Geometry.Bounds]
open scoped BigOperators
namespace SevenEighths.RH20261023Return.TransportHighRowFamily
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
    (hlength : ∑i,length i=(RH20261023Return.Transport.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(RH20261023Return.Transport.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(RH20261023Return.Transport.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+RH20261023Return.Transport.Transport.b)/6-(RH20261023Return.Transport.Arithmetic.y/2-RH20261023Return.Transport.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [RH20261023Return.Transport.Assembly.row_endpoint, RH20261023Return.Transport.Transport.b]
  linarith [RH20261023Return.Transport.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(RH20261023Return.Transport.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(RH20261023Return.Transport.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(RH20261023Return.Transport.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+RH20261023Return.Transport.Arithmetic.x/2+RH20261023Return.Transport.Arithmetic.y)+(RH20261023Return.Transport.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [RH20261023Return.Transport.Assembly.row_endpoint]
  ring

end SevenEighths.RH20261023Return.TransportHighRowFamily
end

end OAI

#print axioms OAI.SevenEighths.RH20261023Return.TransportHighRowFamily.selected_scale_power
#print axioms OAI.SevenEighths.RH20261023Return.TransportHighRowFamily.physical_scale_power
#print axioms OAI.SevenEighths.RH20261023Return.TransportHighRowFamily.small_source_scale
#print axioms OAI.SevenEighths.RH20261023Return.TransportHighRowFamily.large_source_scale
