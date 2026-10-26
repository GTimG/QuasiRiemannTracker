/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual marked-squarefree rows are paid by full singleton rows after exact
inclusion-exclusion. The ordinary amplitude depends only on the row. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.ReferenceBridge
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.SlotDictionary

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open HeckePrimeAnnular
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
local notation "O" => HeckeFamily.O
variable {ι Row : Type*} [Fintype ι]

/-- The literal normalized dependent marked tuple sum. -/
def normalizedMarkedTupleRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) : ℂ :=
  (∏i,(Real.sqrt (P i):ℂ)⁻¹)*∑v : (∀i,S i),
    QRH.Record1252270103TwoIdeal.squarefreeIndicator (∏i,(v i:Ideal O))*
      (∏i,β i (v i))*rowWeight η m A z t (∏i,(v i:Ideal O))

theorem normalizedMarkedTupleRow_eq_injective (η : Character) (m A z : O) (t : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (atoms : Finset (Ideal O)) (hS : ∀i,S i⊆atoms) (hp : ∀p∈atoms,Prime p) :
    normalizedMarkedTupleRow η m A z t S β P=
      injectiveTuplePolynomial
        (fun i (p : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) p) := by
  rw [normalized_injective_slot_dictionary η m A z t S β P atoms hS hp]
  unfold normalizedMarkedTupleRow
  congr 1
  apply Finset.sum_bij (fun v _=>fun i=>(v i:Ideal O))
  · intro v hv
    exact Fintype.mem_piFinset.mpr (fun i=>(v i).property)
  · intro v hv w hw he
    funext i
    exact Subtype.ext (congrFun he i)
  · intro v hv
    exact ⟨fun i=>⟨v i,Fintype.mem_piFinset.mp hv i⟩,Finset.mem_univ _,rfl⟩
  · intro v hv
    rw [map_prod,Finset.prod_mul_distrib]
    ring

/-- The singleton hypotheses use full original normalized slots, with all
row labels unchanged. The row-only factor may include keep, radial weight,
ordinary projectors, centering, and plain normalization. -/
theorem normalized_marked_energy_of_full_singletons
    (η : Row→Character) (m A z : Row→O) (t : Row→ℝ)
    (rows : Finset Row) (D : Row→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (B bound : ℝ) (hB : 1≤B) (hP : ∀i,1≤P i)
    (hβ : ∀i,∀p∈S i,‖β i p‖≤B) (hp : ∀i,∀p∈S i,Prime p)
    (hN : ∀i,∀p∈S i,(p.absNorm:ℝ)≤2*P i)
    (K : ℕ) (hK : Fintype.card ι≤K)
    (hs : ∀E⊆equalityEdges (I:=ι),(∑u∈rows,
      ‖D u*(∏q : {q // singletonBlock (edgeSetoid E) q},
        normalizedSlot (η u) (m u) (A u) (z u)
          (S (singletonRepresentative (edgeSetoid E) q))
          (β (singletonRepresentative (edgeSetoid E) q)) (t u)
          (P (singletonRepresentative (edgeSetoid E) q)))‖^2)≤bound) :
    (∑u∈rows,‖D u*normalizedMarkedTupleRow (η u) (m u) (A u) (z u) (t u) S β P‖^2)≤
      collisionProjectionCost B 256 K*bound := by
  let atoms := Finset.univ.biUnion S
  have hS (i : ι) : S i⊆atoms := Finset.subset_biUnion_of_mem S (Finset.mem_univ i)
  have hprime : ∀p∈atoms,Prime p := by
    intro p hp'
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp'
    exact hp i p hi
  let a := fun u i (p : atoms)=>normalizedRowCoeff (η u) (m u) (A u) (z u) (t u)
    (S i) (β i) (P i) p
  let v := fun i (p : atoms)=>‖normalizedPrimeCoeff (S i) (β i) (P i) p‖
  have he (i : ι) : (∑p : atoms,(v i p)^2)≤256*B^2 := by
    dsimp only [v]
    rw [Finset.sum_coe_sort atoms (fun p=>‖normalizedPrimeCoeff (S i) (β i) (P i) p‖^2)]
    exact normalizedPrimeCoeff_energy atoms (S i) (β i) (P i) B (hP i)
      (zero_le_one.trans hB) (hβ i) (fun p hp'=>(hp i p hp').ne_zero) (hN i)
  have hs' (E : Finset (ι×ι)) (hE : E⊆equalityEdges) :
      (∑u∈rows,‖D u*singletonPolynomial (edgeSetoid E) (a u)‖^2)≤bound := by
    have hd (u : Row) : singletonPolynomial (edgeSetoid E) (a u)=
        ∏q : {q // singletonBlock (edgeSetoid E) q},
          normalizedSlot (η u) (m u) (A u) (z u)
            (S (singletonRepresentative (edgeSetoid E) q))
            (β (singletonRepresentative (edgeSetoid E) q)) (t u)
            (P (singletonRepresentative (edgeSetoid E) q)) := by
      unfold singletonPolynomial
      apply Finset.prod_congr rfl
      intro q hq
      exact (normalizedSlot_sum_atoms (η u) (m u) (A u) (z u) (t u) _ _ _ _ (hS _)).symm
    simpa only [hd] using hs E hE
  have hh := injective_energy_of_full_singletons rows a v D B 256 bound hB (by norm_num)
    (fun _ _=>norm_nonneg _)
    (fun i p=>normalizedPrimeCoeff_bound (S i) (β i) (P i) B (hP i)
      (zero_le_one.trans hB) (hβ i) p) he
    (fun u _ i p=>normalizedRowCoeff_norm (η u) (m u) (A u) (z u) (t u) _ _ _ p)
    K hK hs'
  have hb : 0≤bound := (Finset.sum_nonneg (fun u _=>sq_nonneg _)).trans (hs' ∅ (Finset.empty_subset _))
  have hc := (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr
    (full_edge_family_card_le (J:=ι) K hK)
  have hh' : (∑u∈rows,‖D u*injectiveTuplePolynomial (a u)‖^2)≤
      collisionProjectionCost B 256 K*bound := by
    apply hh.trans
    have hmul := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg ((256*B^K)^K)) hb)
    simpa only [collisionProjectionCost,mul_assoc] using hmul
  simpa only [normalizedMarkedTupleRow_eq_injective (η _) (m _) (A _) (z _) (t _) S β P atoms hS hprime]
    using hh'

/-- One profile constant is chosen before the finite slot type, moving
widths, ray labels, characters, and row-dependent natural frequencies. -/
theorem canonical_marked_energy_of_full_singletons
    (W : ℝ→ℂ) (hW : Continuous W) (hWsupport : Function.support W⊆Set.Icc (1:ℝ) 2)
    (lo hi : ℝ) :
    ∃B : ℝ,1≤B ∧ ∀ (ι Row : Type*) [Fintype ι]
      (rayM : Ideal O) (H : Subgroup (O⧸rayM)ˣ) (χ : ι→Character)
      (η : Row→Character) (m A z : Row→O) (t : Row→ℝ)
      (rows : Finset Row) (D : Row→ℂ) (P σ v : ι→ℝ)
      (bound : ℝ) (K : ℕ),
      (∀i,1≤P i) → (∀i,σ i∈Set.Icc lo hi) → Fintype.card ι≤K →
      let S := fun i=>primePool rayM H 2 (P i)
      let β := fun i I=>idealCoeff (χ i) I*annularWeight W (P i) (σ i) (v i) I
      (∀E⊆equalityEdges (I:=ι),(∑u∈rows,
        ‖D u*(∏q : {q // singletonBlock (edgeSetoid E) q},
          normalizedSlot (η u) (m u) (A u) (z u)
            (S (singletonRepresentative (edgeSetoid E) q))
            (β (singletonRepresentative (edgeSetoid E) q)) (t u)
            (P (singletonRepresentative (edgeSetoid E) q)))‖^2)≤bound) →
      (∑u∈rows,‖D u*normalizedMarkedTupleRow (η u) (m u) (A u) (z u) (t u) S β P‖^2)≤
        collisionProjectionCost B 256 K*bound := by
  obtain ⟨B,hB,hbound⟩ := actual_annular_coefficient_bound W hW hWsupport lo hi
  refine ⟨B,hB,?_⟩
  intro ι Row _ rayM H χ η m A z t rows D P σ v bound K hP hσ hK
  dsimp only
  intro hs
  apply normalized_marked_energy_of_full_singletons η m A z t rows D _ _ P B bound hB hP
    (fun i p _=>hbound (χ i) (P i) (σ i) (v i) (zero_lt_one.trans_le (hP i)) (hσ i) p)
    (fun i p hp=>(Finset.mem_filter.mp hp).2.1)
    (fun i p hp=>(primePool_norm_le rayM H (P i) (zero_le_one.trans (hP i)) p hp).2)
    K hK hs

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.normalizedMarkedTupleRow_eq_injective
#print axioms QRH.Record1252270103Source.Collision.normalized_marked_energy_of_full_singletons
#print axioms QRH.Record1252270103Source.Collision.canonical_marked_energy_of_full_singletons
