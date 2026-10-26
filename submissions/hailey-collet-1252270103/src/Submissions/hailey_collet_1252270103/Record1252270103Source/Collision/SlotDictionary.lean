/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Literal normalized injective slots equal the original prime-pool tuple sum
with its marked-squarefree projector. This is exact finite reindexing. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.ActualCoefficients
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.MarkedSquarefree

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion
open QRH.Record1252270103TwoIdeal
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem sum_atom_tuples (atoms : Finset (Ideal O)) (F : (ι→Ideal O)→ℂ) :
    (∑v : ι→atoms,F (fun i=>(v i:Ideal O)))=
      ∑v∈Fintype.piFinset (fun _ : ι=>atoms),F v := by
  apply Finset.sum_bij (fun v _=>fun i=>(v i:Ideal O))
  · intro v hv
    exact Fintype.mem_piFinset.mpr (fun i=>(v i).property)
  · intro v hv w hw he
    funext i
    exact Subtype.ext (congrFun he i)
  · intro v hv
    exact ⟨fun i=>⟨v i,Fintype.mem_piFinset.mp hv i⟩,Finset.mem_univ _,rfl⟩
  · intro v hv
    rfl

/-- The requested dictionary on actual finite prime pools. Atoms may contain
extra primes; the exact zero extension deletes them before any positivity. -/
theorem normalized_injective_slot_dictionary (η : Character) (m A z : O) (t : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (atoms : Finset (Ideal O)) (hS : ∀i,S i⊆atoms) (hp : ∀p∈atoms,Prime p) :
    injectiveTuplePolynomial
      (fun i (p : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) p)=
      (∏i,(Real.sqrt (P i):ℂ)⁻¹)*
        ∑v∈Fintype.piFinset S,squarefreeIndicator (∏i,v i)*
          ∏i,(β i (v i)*rowWeight η m A z t (v i)) := by
  rw [injective_polynomial_eq_squarefree atoms hp]
  rw [sum_atom_tuples atoms (fun v=>squarefreeIndicator (∏i,v i)*
    ∏i,normalizedRowCoeff η m A z t (S i) (β i) (P i) (v i))]
  have hsub : Fintype.piFinset S⊆Fintype.piFinset (fun _ : ι=>atoms) := by
    intro v hv
    exact Fintype.mem_piFinset.mpr (fun i=>hS i (Fintype.mem_piFinset.mp hv i))
  have he : (∑v∈Fintype.piFinset (fun _ : ι=>atoms),squarefreeIndicator (∏i,v i)*
        ∏i,normalizedRowCoeff η m A z t (S i) (β i) (P i) (v i))=
      ∑v∈Fintype.piFinset S,squarefreeIndicator (∏i,v i)*
        ∏i,normalizedRowCoeff η m A z t (S i) (β i) (P i) (v i) := by
    symm
    apply Finset.sum_subset hsub
    intro v hv hn
    have hn' : ¬∀i,v i∈S i := fun hh=>hn (Fintype.mem_piFinset.mpr hh)
    push Not at hn'
    obtain ⟨i,hi⟩ := hn'
    have hz : (∏i,normalizedRowCoeff η m A z t (S i) (β i) (P i) (v i))=0 := by
      apply Finset.prod_eq_zero (i:=i) (Finset.mem_univ _)
      simp [normalizedRowCoeff,normalizedPrimeCoeff,hi]
    rw [hz,mul_zero]
  rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have ht (i : ι) : normalizedRowCoeff η m A z t (S i) (β i) (P i) (v i)=
      (Real.sqrt (P i):ℂ)⁻¹*(β i (v i)*rowWeight η m A z t (v i)) := by
    simp only [normalizedRowCoeff,normalizedPrimeCoeff,Fintype.mem_piFinset.mp hv i,ite_true,mul_assoc]
  simp_rw [ht]
  rw [Finset.prod_mul_distrib]
  ring

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.sum_atom_tuples
#print axioms QRH.Record1252270103Source.Collision.normalized_injective_slot_dictionary
