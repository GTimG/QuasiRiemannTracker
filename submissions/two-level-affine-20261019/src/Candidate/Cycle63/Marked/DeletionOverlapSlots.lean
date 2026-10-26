import Candidate.Cycle63.Marked.DeletionCollisionEnergy

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O

theorem directPrimeSlot_sum_atoms (u : O) (pool atoms : Finset (Ideal O))
    (β : Ideal O→ℂ) (P : ℝ) (hpool : pool⊆atoms) :
    directPrimeSlot u pool β P =
      ∑p : atoms,idealRowHom u p.val*normalizedPrimeCoeff pool β P p.val := by
  rw [←Finset.sum_subtype (F:=inferInstance) (p:=fun p : Ideal O=>p∈atoms) atoms (by simp)
    (fun p=>idealRowHom u p*normalizedPrimeCoeff pool β P p)]
  unfold directPrimeSlot normalizedPrimeCoeff
  rw [Finset.mul_sum]
  calc
    _ = ∑p∈pool,idealRowHom u p*(if p∈pool then (Real.sqrt P:ℂ)⁻¹*β p else 0) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [hp,ite_true]
      ring
    _ = ∑p∈atoms,idealRowHom u p*(if p∈pool then (Real.sqrt P:ℂ)⁻¹*β p else 0) := by
      apply Finset.sum_subset hpool
      intro p hp hn
      simp [hn]

end
end OAI.SevenEighths.Deletion26
