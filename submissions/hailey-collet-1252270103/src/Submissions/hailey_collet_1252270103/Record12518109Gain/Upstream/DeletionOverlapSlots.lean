/- Adapted from PR63 gao-balanced-marked-20261017; Apache-2.0. Exact source provenance is in evidence/homogeneous-gain/upstream-provenance.json. -/
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.DeletionCollisionEnergy

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Record12518109GainDeletion
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
      apply Finset.sum_congr rfl
      intro p hp
      simp only [hp,ite_true]
      ring
    _ = ∑p∈atoms,idealRowHom u p*(if p∈pool then (Real.sqrt P:ℂ)⁻¹*β p else 0) := by
      apply Finset.sum_subset hpool
      intro p hp hn
      simp [hn]

theorem normalizedPrimeCoeff_filter (pool : Finset (Ideal O)) (β : Ideal O→ℂ)
    (P : ℝ) (keep : Ideal O→Prop) (p : Ideal O) :
    normalizedPrimeCoeff (pool.filter keep) β P p =
      if keep p then normalizedPrimeCoeff pool β P p else 0 := by
  simp only [normalizedPrimeCoeff,Finset.mem_filter]
  split_ifs <;> simp_all

end
end OAI.SevenEighths.Record12518109GainDeletion
