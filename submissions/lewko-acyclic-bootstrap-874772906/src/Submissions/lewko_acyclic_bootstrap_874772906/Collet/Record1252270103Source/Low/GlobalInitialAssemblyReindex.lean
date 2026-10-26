/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact reindexing of the retained marked projector through original-slot embeddings. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialSubsets
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily QRH.Record1252270103TwoIdeal
local notation "O"=>HeckeFamily.O
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {J : Type v} [Fintype J] [DecidableEq J]

theorem markedSlotSum_equiv (η : Character) (m A z : O) (t : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (e : J≃ι) :
    markedSlotSum η m A z t (fun j=>S (e j)) (fun j=>β (e j))=
      markedSlotSum η m A z t S β := by
  let E:=(Equiv.piCongrLeft (fun i=>S i) e)
  unfold markedSlotSum
  rw [←E.sum_comp]
  apply Finset.sum_congr rfl
  intro v hv
  have hp : (∏j,(v j:Ideal O))=∏i,(E v i:Ideal O) := by
    rw [←e.prod_comp (fun i=>(E v i:Ideal O))]
    simp [E]
  have hb : (∏j,β (e j) (v j))=∏i,β i (E v i) := by
    rw [←e.prod_comp (fun i=>β i (E v i))]
    simp [E]
  rw [hp,hb]

theorem markedPositiveRow_equiv (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ) (S : ι→Finset (Ideal O))
    (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) (e : J≃ι) :
    markedPositiveRow η m A z W₁ W₂ b (fun j=>S (e j)) (fun j=>β (e j))
      (fun j=>P (e j)) t X₁ X₂=markedPositiveRow η m A z W₁ W₂ b S β P t X₁ X₂ := by
  unfold markedPositiveRow
  rw [e.prod_comp P,markedSlotSum_equiv η m A z t S β e]

theorem markedPositiveRow_embedding (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ) (S : ι→Finset (Ideal O))
    (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) (f : J↪ι) :
    markedPositiveRow η m A z W₁ W₂ b (fun j=>S (f j)) (fun j=>β (f j))
      (fun j=>P (f j)) t X₁ X₂=
    markedPositiveRow η m A z W₁ W₂ b (fun i:slotRange f=>S i)
      (fun i:slotRange f=>β i) (fun i:slotRange f=>P i) t X₁ X₂ :=
  markedPositiveRow_equiv η m A z W₁ W₂ b (fun i:slotRange f=>S i)
    (fun i:slotRange f=>β i) (fun i:slotRange f=>P i) t X₁ X₂ (slotRangeEquiv f)

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.markedSlotSum_equiv
#print axioms QRH.Record1252270103Low.markedPositiveRow_embedding
