/- Repeated marks: fork of Collet's generic return module Transport.Transport.TailScales (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
open scoped BigOperators
namespace SevenEighths.RepeatedMarksReturn.TransportHighRowFamily
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
    (hlength : ∑i,length i=(RepeatedMarksReturn.Transport.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(RepeatedMarksReturn.Transport.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(RepeatedMarksReturn.Transport.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+RepeatedMarksReturn.Transport.Transport.b)/6-(RepeatedMarksReturn.Transport.Arithmetic.y/2-RepeatedMarksReturn.Transport.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [RepeatedMarksReturn.Transport.Assembly.row_endpoint, RepeatedMarksReturn.Transport.Transport.b]
  linarith [RepeatedMarksReturn.Transport.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(RepeatedMarksReturn.Transport.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(RepeatedMarksReturn.Transport.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(RepeatedMarksReturn.Transport.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+RepeatedMarksReturn.Transport.Arithmetic.x/2+RepeatedMarksReturn.Transport.Arithmetic.y)+(RepeatedMarksReturn.Transport.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [RepeatedMarksReturn.Transport.Assembly.row_endpoint]
  ring

end SevenEighths.RepeatedMarksReturn.TransportHighRowFamily
end

end OAI

