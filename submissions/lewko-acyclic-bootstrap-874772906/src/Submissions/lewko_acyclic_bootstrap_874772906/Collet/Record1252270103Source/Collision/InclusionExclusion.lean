/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact equality-only inclusion-exclusion. Unlike an exact equality pattern,
each term imposes no inequalities and leaves singleton slots unrestricted.
No inequality between a projected polynomial and the original is asserted. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionCollisionAlgebra
import Mathlib.Data.Setoid.Basic

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
variable {I A R : Type*} [Fintype I] [Fintype A] [CommRing R]

def equalityEdges : Finset (I×I) := Finset.univ.filter (fun e=>e.1≠e.2)

def edgePolynomial (E : Finset (I×I)) (a : I→A→R) : R :=
  ∑x : I→A, if ∀e∈E,x e.1=x e.2 then ∏i,a i (x i) else 0

theorem edgePolynomial_empty (a : I→A→R) :
    edgePolynomial ∅ a=∏i,∑p,a i p := by
  simpa [edgePolynomial] using (Fintype.prod_sum a).symm

theorem injective_indicator (x : I→A) :
    (if Function.Injective x then (1:R) else 0)=
      ∏e∈equalityEdges (I:=I),(1-if x e.1=x e.2 then (1:R) else 0) := by
  by_cases h : Function.Injective x
  · rw [ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro e he
    have hn : x e.1≠x e.2 := fun hh=>(Finset.mem_filter.mp he).2 (h hh)
    simp [hn]
  · rw [ite_eq_right h]
    unfold Function.Injective at h
    push Not at h
    obtain ⟨i,j,hx,hn⟩ := h
    symm
    apply Finset.prod_eq_zero (i:=(i,j))
    · simp [equalityEdges,hn]
    · simp [hx]

theorem injective_polynomial_inclusion_exclusion (a : I→A→R) :
    injectiveTuplePolynomial a =
      ∑E∈(equalityEdges (I:=I)).powerset,(-1:R)^E.card*edgePolynomial E a := by
  unfold injectiveTuplePolynomial
  calc
    _ = ∑x : I→A,(∏i,a i (x i))*(if Function.Injective x then (1:R) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    _ = ∑x : I→A,(∏i,a i (x i))*
        ∑E∈(equalityEdges (I:=I)).powerset,(-1:R)^E.card*
          ∏e∈E,(if x e.1=x e.2 then (1:R) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [injective_indicator,Finset.prod_sub]
      simp
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E hE
      unfold edgePolynomial
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.prod_ite_zero]
      split_ifs <;> simp_all <;> ring

/-- The unprojected product is recovered by the same exact identity. -/
theorem full_polynomial_of_injective (a : I→A→R) :
    (∏i,∑p,a i p)=injectiveTuplePolynomial a-
      ∑E∈(equalityEdges (I:=I)).powerset.erase ∅,(-1:R)^E.card*edgePolynomial E a := by
  rw [injective_polynomial_inclusion_exclusion]
  rw [←Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  simp [edgePolynomial_empty]

def edgeSetoid (E : Finset (I×I)) : Setoid I :=
  Relation.EqvGen.setoid (fun i j=>(i,j)∈E)

theorem edge_constraints_iff (E : Finset (I×I)) (x : I→A) :
    (∀e∈E,x e.1=x e.2) ↔ edgeSetoid E≤Setoid.ker x := by
  constructor
  · intro h i j hij
    induction hij with
    | rel i j hij => exact h (i,j) hij
    | refl i => rfl
    | symm i j hij ih => exact ih.symm
    | trans i j k hij hjk ih ij => exact ih.trans ij
  · intro h e he
    exact h (Relation.EqvGen.rel e.1 e.2 he)

def quotientTupleEquiv (r : Setoid I) :
    (Quotient r→A) ≃ {x : I→A // r≤Setoid.ker x} where
  toFun p := ⟨fun i=>p (Quotient.mk r i),fun i j hij=>congrArg p (Quotient.sound hij)⟩
  invFun x := Quotient.lift x.val (fun i j hij=>x.property hij)
  left_inv p := by funext q;induction q using Quotient.inductionOn;rfl
  right_inv x := by apply Subtype.ext;rfl

theorem edgePolynomial_blocks (E : Finset (I×I)) (a : I→A→R) :
    edgePolynomial E a=
      ∏q : Quotient (edgeSetoid E),∑p,∏i∈collisionBlock (edgeSetoid E) q,a i p := by
  unfold edgePolynomial
  simp_rw [edge_constraints_iff]
  rw [←Finset.sum_filter]
  rw [Finset.sum_subtype (F:=inferInstance)
    (p:=fun x : I→A=>edgeSetoid E≤Setoid.ker x) _ (by simp)]
  rw [←(quotientTupleEquiv (A:=A) (edgeSetoid E)).sum_comp]
  change (∑p : Quotient (edgeSetoid E)→A,∏i,a i (p (Quotient.mk _ i)))=_
  simp_rw [product_over_collision_blocks]
  exact (Fintype.prod_sum (fun q : Quotient (edgeSetoid E)=>fun p : A=>
    ∏i∈collisionBlock (edgeSetoid E) q,a i p)).symm

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.injective_polynomial_inclusion_exclusion
#print axioms QRH.Record1252270103Source.Collision.full_polynomial_of_injective
#print axioms QRH.Record1252270103Source.Collision.edgePolynomial_blocks
