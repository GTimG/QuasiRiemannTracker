/- Cycle092 transport re-elaboration by Hailey Collet (2026-11-19), Apache-2.0.
New namespaces and the actual .818 coarse conductor field; original formulas,
source coefficients, analytic statements and inherited notices below retained. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module Transport.Transport.TailScales (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.C092.transport.SelectedActualKernel00
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
set_option autoImplicit false
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Cycle092.SelectedActualKernel.Return.Geometry.CoreBounds]
open scoped BigOperators
namespace SevenEighths.Cycle092SelectedActualReturn.TransportHighRowFamily
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
    (hlength : ∑i,length i=(QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.y:ℝ))^((1/2:ℝ)-1))=Z^(β-(4+QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.b)/6-(QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.y/2-QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.h*(17/50-1/6))+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Assembly.row_endpoint, QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.b]
  linarith [QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.x_add_y]

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0 < Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.y:ℝ))^((2:ℝ)-1))=
      Z^((1+QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.x/2+QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.y)+(QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Arithmetic.h:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  rw [QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Assembly.row_endpoint]
  ring

end SevenEighths.Cycle092SelectedActualReturn.TransportHighRowFamily
end

end OAI
