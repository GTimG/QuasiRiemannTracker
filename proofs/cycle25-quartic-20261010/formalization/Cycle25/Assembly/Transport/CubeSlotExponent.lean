/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Cycle25.Assembly.Transport.GeometryFacts
import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFixedPrimes
import OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection

/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle25HighRowFamily
open ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=Cycle25.ell) :
    (∑j∈slots,ell j/d)=Cycle25.ell/d := by
  rw [←Finset.sum_div,hell]

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=Cycle25.ell) :
    weightedMean slots (fun j=>ell j/d) g= (1/Cycle25.ell)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,ell j=Cycle25.ell) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(Cycle25.ell*(4/25))+weightedMean slots (fun j=>ell j/d) g*Cycle25.ell+mesh*Cycle25.ell) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  field_simp [Cycle25.ell_pos.ne']

lemma source_slot_spike_scale (Z d ell g : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(2*(ell/d)*g)=Z^(2*ell*g) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

end SevenEighths.Cycle25HighRowFamily

end

end OAI
