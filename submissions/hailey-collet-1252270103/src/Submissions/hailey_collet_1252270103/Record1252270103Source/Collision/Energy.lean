/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Both completed-norm directions of collision reduction. All hypotheses on
smaller sources concern complete singleton products, not projected sums. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.BlockEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
open Record1252270103Bootstrap.PR67.RepeatedPrimeSlots
variable {I A Row : Type*} [Fintype I] [Fintype A]

theorem finite_family_energy {C : Type*} (cs : Finset C)
    (rows : Finset Row) (F : C→Row→ℂ) (bound : ℝ)
    (h : ∀c∈cs,(∑u∈rows,‖F c u‖^2)≤bound) :
    (∑u∈rows,‖∑c∈cs,F c u‖^2)≤(cs.card:ℝ)^2*bound := by
  have hh := sum_family_energy (Color:=cs) rows (fun c=>F c.val) bound
    (fun c=>h c.val c.property)
  have he (u : Row) : (∑c : cs,F c.val u)=∑c∈cs,F c u :=
    Finset.sum_coe_sort cs (fun c=>F c u)
  simp_rw [he] at hh
  simpa only [Fintype.card_coe] using hh

theorem signed_edge_family_energy (cs : Finset (Finset (I×I)))
    (rows : Finset Row) (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L bound : ℝ) (hB : 1≤B) (hL : 1≤L)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p) (K : ℕ) (hK : Fintype.card I≤K)
    (hs : ∀E∈cs,(∑u∈rows,‖D u*singletonPolynomial (edgeSetoid E) (a u)‖^2)≤bound) :
    (∑u∈rows,‖∑E∈cs,(-1:ℂ)^E.card*(D u*edgePolynomial E (a u))‖^2)≤
      (cs.card:ℝ)^2*(((L*B^K)^K)^2*bound) := by
  apply finite_family_energy
  intro E hE
  simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] using
    edgePolynomial_energy rows E a v D B L bound hB hL hv0 hv he ha K hK (hs E hE)

/-- The projected energy is bounded by full smaller-source energies only
after the exact alternating sum has been formed. -/
theorem injective_energy_of_full_singletons (rows : Finset Row)
    (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L bound : ℝ) (hB : 1≤B) (hL : 1≤L)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p) (K : ℕ) (hK : Fintype.card I≤K)
    (hs : ∀E⊆equalityEdges,(∑u∈rows,
      ‖D u*singletonPolynomial (edgeSetoid E) (a u)‖^2)≤bound) :
    (∑u∈rows,‖D u*injectiveTuplePolynomial (a u)‖^2)≤
      ((equalityEdges (I:=I)).powerset.card:ℝ)^2*(((L*B^K)^K)^2*bound) := by
  have hid (u : Row) : D u*injectiveTuplePolynomial (a u)=
      ∑E∈(equalityEdges (I:=I)).powerset,(-1:ℂ)^E.card*(D u*edgePolynomial E (a u)) := by
    rw [injective_polynomial_inclusion_exclusion,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    ring
  simp_rw [hid]
  exact signed_edge_family_energy _ rows a v D B L bound hB hL hv0 hv he ha K hK
    (fun E hE=>hs E (Finset.mem_powerset.mp hE))

/-- This is the cardinality-induction step. Every singleton energy on the
right has strictly fewer slots, as proved by singleton_card_lt_of_edges. -/
theorem full_energy_of_injective_and_smaller (rows : Finset Row)
    (a : Row→I→A→ℂ) (v : I→A→ℝ) (D : Row→ℂ)
    (B L projectedBound smallerBound : ℝ) (hB : 1≤B) (hL : 1≤L)
    (hv0 : ∀i p,0≤v i p) (hv : ∀i p,v i p≤B)
    (he : ∀i,(∑p,(v i p)^2)≤L*B^2)
    (ha : ∀u∈rows,∀i p,‖a u i p‖≤v i p) (K : ℕ) (hK : Fintype.card I≤K)
    (hinj : (∑u∈rows,‖D u*injectiveTuplePolynomial (a u)‖^2)≤projectedBound)
    (hs : ∀E⊆equalityEdges,E.Nonempty → (∑u∈rows,
      ‖D u*singletonPolynomial (edgeSetoid E) (a u)‖^2)≤smallerBound) :
    (∑u∈rows,‖D u*(∏i,∑p,a u i p)‖^2)≤
      2*projectedBound+2*((equalityEdges (I:=I)).powerset.erase ∅).card^2*
        (((L*B^K)^K)^2*smallerBound) := by
  let cs := (equalityEdges (I:=I)).powerset.erase ∅
  let diag := fun u=>∑E∈cs,(-1:ℂ)^E.card*(D u*edgePolynomial E (a u))
  have hdiag : (∑u∈rows,‖diag u‖^2)≤(cs.card:ℝ)^2*(((L*B^K)^K)^2*smallerBound) :=
    signed_edge_family_energy cs rows a v D B L smallerBound hB hL hv0 hv he ha K hK
      (fun E hE=>hs E (Finset.mem_powerset.mp (Finset.mem_erase.mp hE).2)
        (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hE).1))
  have hid (u : Row) : D u*(∏i,∑p,a u i p)=
      D u*injectiveTuplePolynomial (a u)-diag u := by
    rw [full_polynomial_of_injective,mul_sub,Finset.mul_sum]
    unfold diag cs
    congr 1
    apply Finset.sum_congr rfl
    intro E hE
    ring
  have hrow (u : Row) : ‖D u*(∏i,∑p,a u i p)‖^2≤
      2*‖D u*injectiveTuplePolynomial (a u)‖^2+2*‖diag u‖^2 := by
    rw [hid u]
    have hh := norm_sub_le (D u*injectiveTuplePolynomial (a u)) (diag u)
    have hn := norm_nonneg (D u*injectiveTuplePolynomial (a u)-diag u)
    have hsq := sq_nonneg (‖D u*injectiveTuplePolynomial (a u)‖-‖diag u‖)
    nlinarith [norm_nonneg (D u*injectiveTuplePolynomial (a u)),norm_nonneg (diag u)]
  calc
    _≤(∑u∈rows,(2*‖D u*injectiveTuplePolynomial (a u)‖^2+2*‖diag u‖^2)) :=
      Finset.sum_le_sum (fun u _=>hrow u)
    _=2*(∑u∈rows,‖D u*injectiveTuplePolynomial (a u)‖^2)+2*(∑u∈rows,‖diag u‖^2) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    _≤2*projectedBound+2*((cs.card:ℝ)^2*(((L*B^K)^K)^2*smallerBound)) := by linarith
    _=_ := by dsimp [cs];push_cast;ring

theorem singleton_width_le (r : Setoid I) (w : I→ℝ) (hw : ∀i,0≤w i) :
    (∑q : {q // singletonBlock r q},w (singletonRepresentative r q))≤∑i,w i :=
  sum_comp_le_total (singletonRepresentative r) (singletonRepresentative_injective r) w hw

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.injective_energy_of_full_singletons
#print axioms QRH.Record1252270103Source.Collision.full_energy_of_injective_and_smaller
#print axioms QRH.Record1252270103Source.Collision.singleton_width_le
