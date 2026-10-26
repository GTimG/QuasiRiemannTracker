/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Joint collision payment for row-dependent live subfamilies of one original
slot family. Full ordinary singleton sums are retained before row counting. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalMarkedSlots
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open Record1252270103Second QRH.Record1252270103Source.Collision
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
local notation "O"=>HeckeFamily.O
universe u v w

/-- Pointwise collision removal retains every full original singleton image.
The finite image sum can subsequently be interchanged with the joint rows. -/
theorem normalized_marked_subfamily_pointwise {α : Type u} {ι : Type v}
    [Fintype α] [Fintype ι] (f : ι↪α)
    (S : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (η : Character) (m A z : O) (t : ℝ) (plain : ℂ)
    (B : ℝ) (hB : 1≤B) (hP : ∀i,1≤P i)
    (hβ : ∀i,∀p∈S i,‖β i p‖≤B) (hp : ∀i,∀p∈S i,Prime p)
    (hN : ∀i,∀p∈S i,(p.absNorm:ℝ)≤2*P i)
    (N : ℕ) (hcard : Fintype.card α≤N) :
    ‖plain*normalizedMarkedTupleRow η m A z t (fun i=>S (f i))
      (fun i=>β (f i)) (fun i=>P (f i))‖^2≤
      collisionProjectionCost B 256 N*
        ∑T : Finset α,‖plain*(∏i:T,normalizedSlot η m A z (S i) (β i) t (P i))‖^2 := by
  classical
  let bound:=∑T : Finset α,‖plain*(∏i:T,normalizedSlot η m A z (S i) (β i) t (P i))‖^2
  have h := normalized_marked_energy_of_full_singletons (fun _ : Unit=>η)
    (fun _=>m) (fun _=>A) (fun _=>z) (fun _=>t) {()} (fun _=>plain)
    (fun i=>S (f i)) (fun i=>β (f i)) (fun i=>P (f i)) B bound hB
    (fun i=>hP (f i)) (fun i=>hβ (f i)) (fun i=>hp (f i)) (fun i=>hN (f i))
    N ((Fintype.card_le_of_injective f f.injective).trans hcard) ?_
  · simpa only [Finset.sum_singleton] using h
  · intro edges hedge
    simp only [Finset.sum_singleton]
    let e : {q // singletonBlock (edgeSetoid edges) q}↪α :=
      ⟨fun q=>f (singletonRepresentative (edgeSetoid edges) q),
        fun x y he=>singletonRepresentative_injective _ (f.injective he)⟩
    let T : Finset α:=Finset.univ.map e
    have he : (∏q : {q // singletonBlock (edgeSetoid edges) q},
        normalizedSlot η m A z (S (f (singletonRepresentative (edgeSetoid edges) q)))
          (β (f (singletonRepresentative (edgeSetoid edges) q))) t
          (P (f (singletonRepresentative (edgeSetoid edges) q))))=
        ∏i:T,normalizedSlot η m A z (S i) (β i) t (P i) := by
      rw [Finset.prod_coe_sort T (fun i=>normalizedSlot η m A z (S i) (β i) t (P i))]
      simp only [T,Finset.prod_map,e]
      rfl
    rw [he]
    dsimp only [bound]
    exact Finset.single_le_sum (f:=fun T:Finset α=>‖plain*(∏i:T,normalizedSlot η m A z (S i) (β i) t (P i))‖^2) (fun _ _=>sq_nonneg _) (Finset.mem_univ T)

/-- All row-dependent live types and embeddings are paid jointly. The only
remaining row-family norms use full subsets of the original slots. -/
theorem marked_subfamily_joint_energy {α : Type u} {Row : Type w} [Fintype α]
    (I : Row→Type v) [∀r,Fintype (I r)] (s : ∀r,Input (I r)) (f : ∀r,I r↪α)
    (S : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hslots : ∀r i,(s r).slots i=S (f r i))
    (hcoeff : ∀r i,restoredSlotCoeff (s r) i=β (f r i))
    (hscale : ∀r i,(s r).P i=P (f r i))
    (K R : Row→Ideal O) (hKR : ∀r,K r∣R r)
    (η : Row→Character) (t : Row→ℝ) (z : Row→O) (plain : Row→ℂ)
    (rows : Finset Row) (weight : Row→ℝ) (hw : ∀r∈rows,0≤weight r)
    (B E : ℝ) (hB : 1≤B) (hE : 0≤E) (hP : ∀i,1≤P i)
    (hβ : ∀i,∀p∈S i,‖β i p‖≤B) (hp : ∀i,∀p∈S i,Prime p)
    (hN : ∀i,∀p∈S i,(p.absNorm:ℝ)≤2*P i)
    (N : ℕ) (hcard : Fintype.card α≤N)
    (hfamily : ∀T : Finset α,(∑r∈rows,‖plain r*
      (∏i:T,normalizedSlot (η r) (fixedBadMask*idealGenerator (R r)) 1 (z r)
        (S i) (β i) (t r) (P i))‖^2*weight r)≤E) :
    (∑r∈rows,‖plain r*markedNewtonSlots (s r) (K r) (R r) (η r) (t r) (z r)‖^2*weight r)≤
      collisionProjectionCost B 256 N*((2:ℝ)^N*E) := by
  classical
  let term:=fun (r:Row) (T:Finset α)=>‖plain r*
    (∏i:T,normalizedSlot (η r) (fixedBadMask*idealGenerator (R r)) 1 (z r)
      (S i) (β i) (t r) (P i))‖^2
  have hc : 0≤collisionProjectionCost B 256 N := by unfold collisionProjectionCost;positivity
  have hpoint (r:Row) : ‖plain r*markedNewtonSlots (s r) (K r) (R r) (η r) (t r) (z r)‖^2≤
      collisionProjectionCost B 256 N*∑T,term r T := by
    have hh:=normalized_marked_subfamily_pointwise (f r) S β P (η r)
      (fixedBadMask*idealGenerator (R r)) 1 (z r) (t r) (plain r) B hB hP hβ hp hN N hcard
    rw [marked_newton_slots_collision (s r) (K r) (R r) (hKR r)]
    by_cases hk : Squarefree (K r)
    · simp only [QRH.Record1252270103TwoIdeal.squarefreeIndicator,hk,ite_true,one_mul]
      have hs : (s r).slots=fun i=>S (f r i):=funext (hslots r)
      have hb : restoredSlotCoeff (s r)=fun i=>β (f r i):=funext (hcoeff r)
      have hps : (s r).P=fun i=>P (f r i):=funext (hscale r)
      rw [hs,hb,hps]
      exact hh
    · simp only [QRH.Record1252270103TwoIdeal.squarefreeIndicator,hk,ite_false,zero_mul,mul_zero,norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg hc (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  calc
    _≤∑r∈rows,(collisionProjectionCost B 256 N*∑T,term r T)*weight r :=
      Finset.sum_le_sum (fun r hr=>mul_le_mul_of_nonneg_right (hpoint r) (hw r hr))
    _=collisionProjectionCost B 256 N*∑T:Finset α,∑r∈rows,term r T*weight r := by
      simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
      rw [Finset.sum_comm]
    _≤collisionProjectionCost B 256 N*∑_T:Finset α,E := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact Finset.sum_le_sum (fun T _=>hfamily T)
    _≤collisionProjectionCost B 256 N*((2:ℝ)^N*E) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard) hE) hc

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.normalized_marked_subfamily_pointwise
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_subfamily_joint_energy
