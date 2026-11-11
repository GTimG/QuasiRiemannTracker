import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
set_option autoImplicit false
namespace OAI
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
open scoped BigOperators
namespace SevenEighths.BoundaryDensitySplitReturn.TransportHighRowFamily
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
    (hlength : ∑i,length i=(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.b)/6-(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y/2-Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.row_endpoint, Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.b]
  linarith [Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x_add_y]
lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x/2+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y)+(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.row_endpoint]
  ring
end SevenEighths.BoundaryDensitySplitReturn.TransportHighRowFamily
end
end OAI
