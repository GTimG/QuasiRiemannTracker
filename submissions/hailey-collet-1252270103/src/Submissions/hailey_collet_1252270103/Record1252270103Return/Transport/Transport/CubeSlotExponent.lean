/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFixedPrimes
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection

/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.Bounds]
open scoped Classical BigOperators
namespace SevenEighths.Record1252270103Return.TransportHighRowFamily
open ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=Record1252270103Return.Transport.Arithmetic.ell) :
    (∑j∈slots,ell j/d)=Record1252270103Return.Transport.Arithmetic.ell/d := by
  rw [←Finset.sum_div,hell]

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=Record1252270103Return.Transport.Arithmetic.ell) :
    weightedMean slots (fun j=>ell j/d) g= (1/Record1252270103Return.Transport.Arithmetic.ell)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,ell j=Record1252270103Return.Transport.Arithmetic.ell) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(Record1252270103Return.Transport.Arithmetic.ell*(4/25))+weightedMean slots (fun j=>ell j/d) g*Record1252270103Return.Transport.Arithmetic.ell+mesh*Record1252270103Return.Transport.Arithmetic.ell) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  field_simp [Record1252270103Return.Transport.Arithmetic.ell_pos.ne']

lemma source_slot_spike_scale (Z d ell g : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(2*(ell/d)*g)=Z^(2*ell*g) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

end SevenEighths.Record1252270103Return.TransportHighRowFamily

end

end OAI

#print axioms OAI.SevenEighths.Record1252270103Return.TransportHighRowFamily.source_slot_length_sum
#print axioms OAI.SevenEighths.Record1252270103Return.TransportHighRowFamily.source_slot_weightedMean
#print axioms OAI.SevenEighths.Record1252270103Return.TransportHighRowFamily.source_slot_product
#print axioms OAI.SevenEighths.Record1252270103Return.TransportHighRowFamily.source_slot_spike_scale
