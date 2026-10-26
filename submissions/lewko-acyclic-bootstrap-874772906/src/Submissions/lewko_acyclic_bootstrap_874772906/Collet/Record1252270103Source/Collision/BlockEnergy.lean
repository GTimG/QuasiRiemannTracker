/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Equality-only collision blocks cost a constant and leave full singleton
polynomials. The PR67 collision mass proof is reused with its exact premises. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.InclusionExclusion
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionCollisionEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
variable {I A : Type*} [Fintype I] [Fintype A]

def singletonPolynomial (r : Setoid I) (a : I→A→ℂ) : ℂ :=
  ∏q : {q // singletonBlock r q},∑p,a (singletonRepresentative r q) p

def collisionPolynomial (r : Setoid I) (a : I→A→ℂ) : ℂ :=
  ∏q : {q // ¬singletonBlock r q},∑p,∏i∈collisionBlock r q.val,a i p

theorem edgePolynomial_split (E : Finset (I×I)) (a : I→A→ℂ) :
    edgePolynomial E a=singletonPolynomial (edgeSetoid E) a*
      collisionPolynomial (edgeSetoid E) a := by
  rw [edgePolynomial_blocks,←Fintype.prod_subtype_mul_prod_subtype
    (singletonBlock (edgeSetoid E))]
  unfold singletonPolynomial collisionPolynomial
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  simp_rw [singletonBlock_eq]
  simp

theorem collisionPolynomial_norm_le (r : Setoid I) (a : I→A→ℂ) (v : I→A→ℝ)
    (B L : ℝ) (hB : 1≤B) (hL : 1≤L)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀i p,‖a i p‖≤v i p) (K : ℕ) (hK : Fintype.card I≤K) :
    ‖collisionPolynomial r a‖≤(L*B^K)^K := by
  unfold collisionPolynomial
  rw [norm_prod]
  calc
    _≤∏q : {q // ¬singletonBlock r q},∑p,∏i∈collisionBlock r q.val,v i p := by
      apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      intro q hq
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>ha i p)
    _=∑t : {q // ¬singletonBlock r q}→A,
        ∏q : {q // ¬singletonBlock r q},∏i∈collisionBlock r q.val,v i (t q) :=
      Fintype.prod_sum _
    _≤_ := collision_assignments_mass r v B L hB hL hv0 hv he K hK

/-- A pointwise bound is valid only after exact factorization of each
equality-only term; the remaining singleton sum has no deletions or colors. -/
theorem edgePolynomial_norm_le (E : Finset (I×I)) (a : I→A→ℂ) (v : I→A→ℝ)
    (D : ℂ) (B L : ℝ) (hB : 1≤B) (hL : 1≤L)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀i p,‖a i p‖≤v i p) (K : ℕ) (hK : Fintype.card I≤K) :
    ‖D*edgePolynomial E a‖≤(L*B^K)^K*‖D*singletonPolynomial (edgeSetoid E) a‖ := by
  rw [edgePolynomial_split,←mul_assoc,norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (collisionPolynomial_norm_le (edgeSetoid E) a v B L hB hL hv0 hv he ha K hK)
    (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem edgePolynomial_energy {Row : Type*} (rows : Finset Row)
    (E : Finset (I×I)) (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L bound : ℝ) (hB : 1≤B) (hL : 1≤L)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p) (K : ℕ) (hK : Fintype.card I≤K)
    (hs : (∑u∈rows,‖D u*singletonPolynomial (edgeSetoid E) (a u)‖^2)≤bound) :
    (∑u∈rows,‖D u*edgePolynomial E (a u)‖^2)≤((L*B^K)^K)^2*bound := by
  have hm : 0≤(L*B^K)^K := pow_nonneg
    (mul_nonneg (zero_le_one.trans hL) (pow_nonneg (zero_le_one.trans hB) _)) _
  calc
    _≤∑u∈rows,((L*B^K)^K)^2*‖D u*singletonPolynomial (edgeSetoid E) (a u)‖^2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hm (norm_nonneg _))).mpr
        (edgePolynomial_norm_le E (a u) v (D u) B L hB hL hv0 hv he (ha u hu) K hK)
    _=((L*B^K)^K)^2*(∑u∈rows,‖D u*singletonPolynomial (edgeSetoid E) (a u)‖^2) :=
      (Finset.mul_sum _ _ _).symm
    _≤_ := mul_le_mul_of_nonneg_left hs (sq_nonneg _)

/-- Every nonempty inclusion-exclusion edge set removes at least one slot.
The source induction may therefore use smaller cardinality at the same face. -/
theorem singleton_card_lt_of_edges (E : Finset (I×I))
    (hE : E⊆equalityEdges) (hne : E.Nonempty) :
    Fintype.card {q // singletonBlock (edgeSetoid E) q}<Fintype.card I := by
  obtain ⟨⟨i,j⟩,hij⟩ := hne
  have hneij : i≠j := (Finset.mem_filter.mp (hE hij)).2
  apply Fintype.card_lt_of_injective_not_surjective
    (singletonRepresentative (edgeSetoid E)) (singletonRepresentative_injective _)
  intro hs
  obtain ⟨q,hq⟩ := hs i
  have hj : j∈collisionBlock (edgeSetoid E) q.val := by
    simp only [collisionBlock,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←singletonRepresentative_class _ q,hq]
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel i j hij))
  rw [singletonBlock_eq] at hj
  have hji := Finset.mem_singleton.mp hj
  exact hneij (hq.symm.trans hji.symm)

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.edgePolynomial_split
#print axioms QRH.Record1252270103Source.Collision.collisionPolynomial_norm_le
#print axioms QRH.Record1252270103Source.Collision.edgePolynomial_norm_le
#print axioms QRH.Record1252270103Source.Collision.edgePolynomial_energy
#print axioms QRH.Record1252270103Source.Collision.singleton_card_lt_of_edges
