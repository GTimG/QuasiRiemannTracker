import QRH.NumericFacts
import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
import QRH.Geometry
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.QRHProbeHighRowFamily
open HeckeDetectorPhysicalSelection
section
variable {Slot : Type*} (slots : Finset Slot)
include Slot slots

lemma source_slot_length_sum (lengths : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,lengths j=QRH.ell) :
    (∑j∈slots,lengths j/d)=QRH.ell/d := by rw [←Finset.sum_div,hell]
section
variable (lengths g : Slot→ℝ)
include lengths g

lemma source_slot_weightedMean
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,lengths j=QRH.ell) :
    weightedMean slots (fun j=>lengths j/d) g=(∑j∈slots,lengths j*g j)/QRH.ell := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  have he := QRH.NumericFacts.ell_ne_zero
  field_simp
lemma source_slot_product
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,lengths j=QRH.ell) :
    (∏j∈slots,(Z^(lengths j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(4/25:ℝ)*QRH.ell+weightedMean slots (fun j=>lengths j/d) g*QRH.ell+mesh*QRH.ell) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots lengths g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  have he := QRH.NumericFacts.ell_ne_zero
  field_simp
end

end

end SevenEighths.QRHProbeHighRowFamily
end
end OAI
