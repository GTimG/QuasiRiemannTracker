/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Transport.GeometryFacts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFixedPrimes
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Transport_CubeSlotExponent : Cycle63.AffineLedger := Cycle153.Root.rootLedger


/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle153EndpointHighRowFamily
open ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=Cycle153Endpoint.Arithmetic.ell) :
    (∑j∈slots,ell j/d)=Cycle153Endpoint.Arithmetic.ell/d := by
  rw [←Finset.sum_div,hell]

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=Cycle153Endpoint.Arithmetic.ell) :
    weightedMean slots (fun j=>ell j/d) g= (1/Cycle153Endpoint.Arithmetic.ell)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,ell j=Cycle153Endpoint.Arithmetic.ell) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(Cycle153Endpoint.Arithmetic.ell*(4/25))+weightedMean slots (fun j=>ell j/d) g*Cycle153Endpoint.Arithmetic.ell+mesh*Cycle153Endpoint.Arithmetic.ell) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  field_simp [Cycle153Endpoint.Arithmetic.ell_pos.ne']

end SevenEighths.Cycle153EndpointHighRowFamily

end

end OAI
