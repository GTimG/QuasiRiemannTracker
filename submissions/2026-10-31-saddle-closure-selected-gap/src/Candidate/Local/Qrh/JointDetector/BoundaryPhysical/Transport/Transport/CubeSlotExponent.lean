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
/- Repeated marks: fork of Collet's generic return module Transport.Transport.CubeSlotExponent (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFixedPrimes
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
set_option autoImplicit false

/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
open scoped Classical BigOperators
namespace SevenEighths.BoundaryDensitySplitReturn.TransportHighRowFamily
open ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell) :
    (∑j∈slots,ell j/d)=Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell/d := by
  rw [←Finset.sum_div,hell]

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell) :
    weightedMean slots (fun j=>ell j/d) g= (1/Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,ell j=Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell*(4/25))+weightedMean slots (fun j=>ell j/d) g*Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell+mesh*Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  field_simp [Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell_pos.ne']

lemma source_slot_spike_scale (Z d ell g : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(2*(ell/d)*g)=Z^(2*ell*g) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

end SevenEighths.BoundaryDensitySplitReturn.TransportHighRowFamily

end

end OAI
