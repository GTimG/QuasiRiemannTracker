/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Arbitrary finite slot embeddings reindex the literal energy without coefficient changes. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialProjectedDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.ReferenceBridge
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.CompletedEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentHeckeExpansion
open QRH.Record1252270103Restoration QRH.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
universe u v
variable {ι : Type u} [Fintype ι] {J : Type v} [Fintype J]

def slotRange (f : J↪ι) : Finset ι := Finset.univ.image f

def slotRangeEquiv (f : J↪ι) : J≃slotRange f :=
  Equiv.ofBijective (fun j=>⟨f j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun x y h=>f.injective (congrArg Subtype.val h),by
      intro x
      obtain ⟨j,hj,he⟩:=Finset.mem_image.mp x.property
      exact ⟨j,Subtype.ext he⟩⟩

@[simp] theorem slotRangeEquiv_coe (f : J↪ι) (j : J) : (slotRangeEquiv f j:ι)=f j := rfl

theorem squarefreeEnergy_equiv_slots (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (e : J≃ι) :
    squarefreeEnergy η m A t W₁ W₂ b (fun j=>S (e j)) (fun j=>β (e j))
      (fun j=>P (e j)) X₁ X₂ keep Φ K=
    squarefreeEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ K := by
  unfold squarefreeEnergy squarefreePositiveSlotRow
  apply tsum_congr
  intro z
  rw [e.prod_comp P,e.prod_comp (fun i=>rowSlot η m A z (S i) (β i) t)]

/-- The reference supplier sees the exact image subset of the original slots. -/
theorem squarefreeEnergy_embedding (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (f : J↪ι) :
    squarefreeEnergy η m A t W₁ W₂ b (fun j=>S (f j)) (fun j=>β (f j))
      (fun j=>P (f j)) X₁ X₂ keep Φ K=
    squarefreeEnergy η m A t W₁ W₂ b (fun i:slotRange f=>S i) (fun i:slotRange f=>β i)
      (fun i:slotRange f=>P i) X₁ X₂ keep Φ K :=
  squarefreeEnergy_equiv_slots η m A t W₁ W₂ b X₁ X₂ keep Φ K
    (fun i:slotRange f=>S i) (fun i:slotRange f=>β i) (fun i:slotRange f=>P i) (slotRangeEquiv f)

/-- Literal full-subset energy bounds imply the finite positive inlet used by
collision inclusion-exclusion; this is a reindex and positivity dictionary. -/
theorem fullSubsetBound_of_squarefree_subsets
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (atoms : Finset (Ideal O)) (hS : ∀i,S i⊆atoms)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (bound : ℝ)
    (hfull : ∀F : Finset ι,squarefreeEnergy η m A t W₁ W₂ b
      (fun i:F=>S i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ keep Φ K≤bound)
    (rows : Finset O) :
    fullSubsetBound rows (fun z i (p : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) p)
      (weightedPlain η m A t W₁ W₂ b X₁ X₂ keep Φ K) bound := by
  intro J _ f
  have he:=squarefreeEnergy_embedding η m A t W₁ W₂ b X₁ X₂ keep Φ K S β P f
  have hs:=squarefree_energy_summable η m A W₁ W₂ b
    (fun j=>S (f j)) (fun j=>β (f j)) (fun j=>P (f j)) t X₁ X₂ keep Φ K hK
  have hfin:=hs.sum_le_tsum rows (fun z _=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl)
  have hd (z : O) :
      ‖weightedPlain η m A t W₁ W₂ b X₁ X₂ keep Φ K z*
        (∏j,∑p : atoms,normalizedRowCoeff η m A z t (S (f j)) (β (f j)) (P (f j)) p)‖^2=
      if keep z then ‖squarefreePositiveSlotRow η m A z W₁ W₂ b (fun j=>S (f j))
        (fun j=>β (f j)) (fun j=>P (f j)) t X₁ X₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0 := by
    simp_rw [←normalizedSlot_sum_atoms η m A z t _ atoms _ _ (hS _)]
    exact weightedPlain_row_norm η m A z t W₁ W₂ b X₁ X₂ keep Φ K
      (fun j=>S (f j)) (fun j=>β (f j)) (fun j=>P (f j)) hX₁ hX₂ (fun j=>(hP (f j)).le) hΦ
  simp_rw [hd]
  exact hfin.trans (he.trans_le (hfull (slotRange f)))

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.squarefreeEnergy_embedding
#print axioms QRH.Record1252270103Low.fullSubsetBound_of_squarefree_subsets
