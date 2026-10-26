import Candidate.Cycle63.Marked.DeletionCollisionAlgebra
import Candidate.Cycle63.Marked.DeletionCollisionBounds
import Candidate.Cycle63.Marked.ColoringEnergy

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators

/-- Weighted finite Cauchy-Schwarz. The number of assignments does not
enter the bound; only the sum of their scalar masses does. -/
theorem weighted_family_energy {Row T : Type*} [Fintype T]
    (rows : Finset Row) (F G : T→Row→ℂ) (w : T→ℝ) (E : ℝ)
    (hw : ∀t,0≤w t) (hFG : ∀t,∀u∈rows,‖F t u‖≤w t*‖G t u‖)
    (hG : ∀t,(∑u∈rows,‖G t u‖^2)≤E) :
    (∑u∈rows,‖∑t,F t u‖^2)≤(∑t,w t)^2*E := by
  have hp (u : Row) (hu : u∈rows) : ‖∑t,F t u‖^2≤
      (∑t,w t)*(∑t,w t*‖G t u‖^2) := by
    have hn : ‖∑t,F t u‖≤∑t,w t*‖G t u‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _=>hFG t u hu))
    apply ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
      (fun t _=>mul_nonneg (hw t) (norm_nonneg _)))).mpr hn).trans
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun t _=>hw t) (fun t _=>mul_nonneg (hw t) (sq_nonneg _))
    intro t ht
    exact le_of_eq (by ring)
  calc
    _≤∑u∈rows,(∑t,w t)*(∑t,w t*‖G t u‖^2) := Finset.sum_le_sum hp
    _=(∑t,w t)*(∑t,w t*(∑u∈rows,‖G t u‖^2)) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      simp_rw [←Finset.mul_sum]
    _≤(∑t,w t)*(∑t,w t*E) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun t _=>mul_le_mul_of_nonneg_left (hG t) (hw t)))
      (Finset.sum_nonneg (fun t _=>hw t))
    _=_ := by rw [←Finset.sum_mul];ring

variable {I A : Type*} [Fintype I] [Fintype A]

def singletonBlock (r : Setoid I) (q : Quotient r) : Prop :=
  (collisionBlock r q).card=1

def singletonRepresentative (r : Setoid I) (q : {q // singletonBlock r q}) : I :=
  (Finset.card_eq_one.mp q.property).choose

theorem singletonBlock_eq (r : Setoid I) (q : {q // singletonBlock r q}) :
    collisionBlock r q.val={singletonRepresentative r q} :=
  (Finset.card_eq_one.mp q.property).choose_spec

theorem singletonRepresentative_class (r : Setoid I) (q : {q // singletonBlock r q}) :
    Quotient.mk r (singletonRepresentative r q)=q.val := by
  have h : singletonRepresentative r q∈collisionBlock r q.val := by rw [singletonBlock_eq];simp
  simpa [collisionBlock] using h

theorem singletonRepresentative_injective (r : Setoid I) :
    Function.Injective (singletonRepresentative r) := by
  intro q q' h
  apply Subtype.ext
  rw [←singletonRepresentative_class r q,←singletonRepresentative_class r q',h]

theorem collisionBlock_card_two (r : Setoid I) (q : {q // ¬singletonBlock r q}) :
    2≤(collisionBlock r q.val).card := by
  have hp := (collisionBlock_nonempty r q.val).card_pos
  have hn := q.property
  unfold singletonBlock at hn
  omega

theorem quotient_card_le (r : Setoid I) : Fintype.card (Quotient r)≤Fintype.card I :=
  Fintype.card_le_of_surjective (Quotient.mk r) Quotient.mk_surjective

theorem singleton_card_le (r : Setoid I) :
    Fintype.card {q // singletonBlock r q}≤Fintype.card I :=
  Fintype.card_le_of_injective _ (singletonRepresentative_injective r)

theorem setoid_card_le (K : ℕ) (hK : Fintype.card I≤K) :
    Fintype.card (Setoid I)≤2^(K*K) := by
  have h := Fintype.card_le_of_injective (fun r : Setoid I=>r.r)
    (fun _ _ hh=>Setoid.eq_iff_rel_eq.mpr hh)
  have heq : Fintype.card (I→ I→Prop)=2^(Fintype.card I*Fintype.card I) := by
    simp [pow_mul]
  rw [heq] at h
  exact h.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_self_le_mul_self hK))

/-- Uniform total mass of all collision assignments for a fixed equality
pattern. Singleton blocks retain the actual row phase. -/
theorem collision_assignments_mass (r : Setoid I) (v : I→A→ℝ)
    (B L : ℝ) (hB : 1≤B) (hL : 1≤L)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2) (K : ℕ) (hK : Fintype.card I≤K) :
    (∑t : {q // ¬singletonBlock r q}→A,
      ∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,v i (t q))≤
        (L*B^K)^K := by
  rw [←Fintype.prod_sum (fun q : {q // ¬singletonBlock r q}=>fun p : A=>
    ∏i∈collisionBlock r q.val,v i p)]
  have hbase : 1≤L*B^K := one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ hB)
  calc
    _≤∏q : {q // ¬singletonBlock r q},L*B^K := by
      apply Finset.prod_le_prod₀
      · intro q hq
        exact Finset.sum_nonneg (fun p _=>Finset.prod_nonneg (fun i _=>hv0 i p))
      · intro q hq
        apply (collision_block_mass (collisionBlock r q.val) v B L
          (zero_le_one.trans hB) (zero_le_one.trans hL) (collisionBlock_card_two r q)
          (fun i _=>hv0 i) (fun i _=>hv i) (fun i _=>he i)).trans
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB
          ((Finset.card_le_univ _).trans hK)) (zero_le_one.trans hL)
    _=(L*B^K)^Fintype.card {q // ¬singletonBlock r q} := by simp
    _≤(L*B^K)^K := pow_le_pow_right₀ hbase
      ((Fintype.card_subtype_le _).trans ((quotient_card_le r).trans hK))

/-- Removing collisions reduces the complete product moment to the
injective singleton moments. Every cost depends only on the slot count. -/
theorem product_energy_of_singletons {Row : Type*}
    (rows : Finset Row) (a : Row→ I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L E : ℝ) (hB : 1≤B) (hL : 1≤L) (hE : 0≤E)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p)
    (K : ℕ) (hK : Fintype.card I≤K)
    (hsingle : ∀r : Setoid I,∀t : {q // ¬singletonBlock r q}→A,
      (∑u∈rows,‖D u*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q}=>fun p=>
          if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a u (singletonRepresentative r q) p else 0)‖^2)≤E) :
    (∑u∈rows,‖D u*(∏i,∑p,a u i p)‖^2)≤
      ((2:ℝ)^(K*K)*(L*B^K)^K)^2*E := by
  let M : ℝ := (L*B^K)^K
  have hM : 0≤ M := by dsimp [M];positivity
  have hr (r : Setoid I) :
      (∑u∈rows,‖D u*injectiveTuplePolynomial
        (fun q : Quotient r=>fun p=>∏i∈collisionBlock r q,a u i p)‖^2)≤ M^2*E := by
    let G (t : {q // ¬singletonBlock r q}→A) (u : Row) : ℂ :=
      D u*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q}=>fun p=>
          if ∀j : {q // ¬singletonBlock r q},p≠t j then
            a u (singletonRepresentative r q) p else 0)
    let F (t : {q // ¬singletonBlock r q}→A) (u : Row) : ℂ :=
      if Function.Injective t then
        (∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,a u i (t q))*G t u
      else 0
    let mass (t : {q // ¬singletonBlock r q}→A) : ℝ :=
      ∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,v i (t q)
    have hm0 (t) : 0≤ mass t := Finset.prod_nonneg
      (fun q _=>Finset.prod_nonneg (fun i _=>hv0 i (t q)))
    have hFG (t) (u) (hu : u∈rows) : ‖F t u‖≤ mass t*‖G t u‖ := by
      dsimp only [F]
      split_ifs
      · rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simp only [norm_prod]
        exact Finset.prod_le_prod₀ (fun q _=>Finset.prod_nonneg (fun i _=>norm_nonneg _))
          (fun q _=>Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>ha u hu i (t q)))
      · simpa using mul_nonneg (hm0 t) (norm_nonneg (G t u))
    have hh := weighted_family_energy rows F G mass E hm0 hFG (hsingle r)
    have hmass : (∑t,mass t)≤ M := collision_assignments_mass r v B L hB hL hv0 hv he K hK
    have hbound : (∑u∈rows,‖∑t,F t u‖^2)≤ M^2*E := hh.trans
      (mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (Finset.sum_nonneg (fun t _=>hm0 t)) hM).mpr hmass) hE)
    convert hbound using 1
    refine Finset.sum_congr rfl fun u hu => ?_
    congr 2
    rw [injectiveTuplePolynomial_split (singletonBlock r),Finset.mul_sum]
    apply Finset.sum_congr (by ext;simp)
    intro t ht
    dsimp only [F,G]
    have hs : (fun q : {q // singletonBlock r q}=>fun p : A=>
        if ∀j : {q // ¬singletonBlock r q},p≠t j then
          (∏i∈collisionBlock r q.val,a u i p) else 0) =
      (fun q : {q // singletonBlock r q}=>fun p : A=>
        if ∀j : {q // ¬singletonBlock r q},p≠t j then
          a u (singletonRepresentative r q) p else 0) := by
      funext q p
      rw [singletonBlock_eq]
      simp
    rw [hs]
    split_ifs <;> ring
  have hh := RepeatedPrimeSlots.sum_family_energy rows
    (fun r : Setoid I=>fun u=>D u*injectiveTuplePolynomial
      (fun q : Quotient r=>fun p=>∏i∈collisionBlock r q,a u i p)) (M^2*E) hr
  have hcard : (Fintype.card (Setoid I):ℝ)≤(2:ℝ)^(K*K) := by
    exact_mod_cast setoid_card_le (I:=I) K hK
  have hbound := hh.trans (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hcard) (mul_nonneg (sq_nonneg M) hE))
  have heq (u : Row) : (∑r : Setoid I,D u*injectiveTuplePolynomial
      (fun q : Quotient r=>fun p=>∏i∈collisionBlock r q,a u i p)) =D u*(∏i,∑p,a u i p) := by
    rw [←Finset.mul_sum,←product_sum_collision_blocks]
  simp_rw [heq] at hbound
  convert hbound using 1
  dsimp [M]
  ring

end
end OAI.SevenEighths.Deletion26
