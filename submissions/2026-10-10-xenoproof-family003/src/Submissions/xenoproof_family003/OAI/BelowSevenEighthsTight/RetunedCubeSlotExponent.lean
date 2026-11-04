import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection

/- Arbitrary total slot length in the ORIGINAL physical weightedMean. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum_retuned {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (total d : ℝ) (hell : ∑j∈slots,ell j=total) :
    (∑j∈slots,ell j/d)=total/d := by
  rw [←Finset.sum_div,hell]

lemma source_slot_weightedMean_retuned {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (total d : ℝ) (htotal : total≠0) (hd : d≠0) (hell : ∑j∈slots,ell j=total) :
    weightedMean slots (fun j=>ell j/d) g=(∑j∈slots,ell j*g j)/total := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product_retuned {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (total Z d mesh : ℝ) (htotal : total≠0) (hZ : 0<Z) (hd : d≠0)
    (hell : ∑j∈slots,ell j=total) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(total*(-(4/25:ℝ)+weightedMean slots (fun j=>ell j/d) g+mesh)) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean_retuned slots ell g total d htotal hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  field_simp
  <;> ring

end SevenEighths.ProbeHighRowFamily
end
end OAI

#print axioms OAI.SevenEighths.ProbeHighRowFamily.source_slot_length_sum_retuned
#print axioms OAI.SevenEighths.ProbeHighRowFamily.source_slot_weightedMean_retuned
#print axioms OAI.SevenEighths.ProbeHighRowFamily.source_slot_product_retuned
