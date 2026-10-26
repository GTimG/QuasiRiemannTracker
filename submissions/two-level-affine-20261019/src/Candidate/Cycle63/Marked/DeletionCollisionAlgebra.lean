import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators

variable {I A R : Type*} [Fintype I] [Fintype A] [CommSemiring R]

instance finiteSetoid : Fintype (Setoid I) :=
  Fintype.ofInjective (fun r : Setoid I=>r.r) (fun _ _ h=>Setoid.eq_iff_rel_eq.mpr h)

/-- Tuples with a prescribed equality pattern are injective assignments
to the quotient blocks of that pattern. -/
def kernelTupleEquiv (r : Setoid I) :
    {p : Quotient r→A // Function.Injective p} ≃ {x : I→A // Setoid.ker x=r} where
  toFun p := ⟨fun i=>p.val (Quotient.mk r i),by
    apply Setoid.ext
    intro i j
    change (p.val (Quotient.mk r i)=p.val (Quotient.mk r j))↔r i j
    exact ⟨fun h=>Quotient.exact (p.property h),fun h=>congrArg p.val (Quotient.sound h)⟩⟩
  invFun x := ⟨Quotient.lift x.val (fun i j hij=>by
    have hh : Setoid.ker x.val i j := by rw [x.property];exact hij
    exact hh),by
    intro q q' h
    induction q using Quotient.inductionOn with | h i =>
      induction q' using Quotient.inductionOn with | h j =>
        apply Quotient.sound
        change x.val i=x.val j at h
        have hh : Setoid.ker x.val i j := h
        rwa [x.property] at hh⟩
  left_inv p := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Exact decomposition of the full slot product by equality pattern,
with the coefficient in each quotient block kept as a product. -/
theorem product_sum_kernel (a : I→A→R) :
    (∏i,∑p,a i p) = ∑r : Setoid I,
      ∑p : {p : Quotient r→A // Function.Injective p},
        ∏i,a i (p.val (Quotient.mk r i)) := by
  rw [Fintype.prod_sum]
  have hf := Finset.sum_fiberwise (Finset.univ : Finset (I→A))
    (fun x=>Setoid.ker x) (fun x=>∏i,a i (x i))
  rw [←hf]
  apply Finset.sum_congr (by ext;simp)
  intro r hr
  rw [Finset.sum_subtype (p:=fun x : I→A=>Setoid.ker x=r) _ (by simp) (fun x : I→A=>∏i,a i (x i))]
  exact ((kernelTupleEquiv r).sum_comp (fun x : {x : I→A // Setoid.ker x=r}=>∏i,a i (x.val i))).symm

def collisionBlock (r : Setoid I) (q : Quotient r) : Finset I :=
  Finset.univ.filter (fun i=>Quotient.mk r i=q)

theorem collisionBlock_nonempty (r : Setoid I) (q : Quotient r) :
    (collisionBlock r q).Nonempty := by
  obtain ⟨i,rfl⟩ := Quotient.exists_rep q
  exact ⟨i,by simp [collisionBlock]⟩

omit [Fintype A] in
theorem product_over_collision_blocks (r : Setoid I) (a : I→A→R) (p : Quotient r→A) :
    (∏i,a i (p (Quotient.mk r i))) =
      ∏q : Quotient r,∏i∈collisionBlock r q,a i (p q) := by
  rw [←Fintype.prod_fiberwise (Quotient.mk r) (fun i=>a i (p (Quotient.mk r i)))]
  apply Finset.prod_congr (by ext;simp)
  intro q hq
  rw [Finset.prod_subtype (F:=inferInstance) (p:=fun i : I=>Quotient.mk r i=q)
    (collisionBlock r q) (by intro i;simp [collisionBlock])]
  apply Finset.prod_congr (by ext;simp)
  intro i hi
  rw [i.property]

def injectiveTuplePolynomial (a : I→A→R) : R :=
  ∑x : I→A,if Function.Injective x then ∏i,a i (x i) else 0

theorem product_sum_collision_blocks (a : I→A→R) :
    (∏i,∑p,a i p) = ∑r : Setoid I,
      injectiveTuplePolynomial (fun q : Quotient r=>fun p=>∏i∈collisionBlock r q,a i p) := by
  rw [product_sum_kernel]
  apply Finset.sum_congr (by ext;simp)
  intro r hr
  unfold injectiveTuplePolynomial
  rw [←Finset.sum_filter]
  rw [Finset.sum_subtype (F:=inferInstance) (p:=fun x : Quotient r→A=>Function.Injective x) _ (by simp)]
  apply Finset.sum_congr (by ext;simp)
  intro p hp
  exact product_over_collision_blocks r a p.val

variable (P : I→Prop)

def joinAssignments (s : {i // P i}→A) (t : {i // ¬P i}→A) (i : I) : A :=
  if h : P i then s ⟨i,h⟩ else t ⟨i,h⟩

omit [Fintype I] [Fintype A] in
theorem injective_joinAssignments (s : {i // P i}→A) (t : {i // ¬P i}→A) :
    Function.Injective (joinAssignments P s t) ↔
      Function.Injective s ∧ Function.Injective t ∧ ∀i j,s i≠t j := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i j he
      apply Subtype.ext
      apply h
      simpa [joinAssignments,i.property,j.property] using he
    · intro i j he
      apply Subtype.ext
      apply h
      simpa [joinAssignments,i.property,j.property] using he
    · intro i j he
      have hh : i.val=j.val := h (by simpa [joinAssignments,i.property,j.property] using he)
      exact j.property (hh ▸ i.property)
  · rintro ⟨hs,ht,hcross⟩ i j he
    by_cases hi : P i <;> by_cases hj : P j
    · have hh := hs (show s ⟨i,hi⟩=s ⟨j,hj⟩ by simpa [joinAssignments,hi,hj] using he)
      exact congrArg Subtype.val hh
    · exact False.elim (hcross ⟨i,hi⟩ ⟨j,hj⟩ (by simpa [joinAssignments,hi,hj] using he))
    · exact False.elim (hcross ⟨j,hj⟩ ⟨i,hi⟩ (by simpa [joinAssignments,hi,hj] using he.symm))
    · have hh := ht (show t ⟨i,hi⟩=t ⟨j,hj⟩ by simpa [joinAssignments,hi,hj] using he)
      exact congrArg Subtype.val hh

def assignmentSplit : (I→A) ≃ ({i // P i}→A)×({i // ¬P i}→A) where
  toFun x := (fun i=>x i.val,fun i=>x i.val)
  invFun st := joinAssignments P st.1 st.2
  left_inv x := by funext i;simp [joinAssignments]
  right_inv st := by ext i <;> simp [joinAssignments,i.property]

omit [Fintype A] in
theorem joinAssignments_product (a : I→A→R) (s : {i // P i}→A) (t : {i // ¬P i}→A) :
    (∏i,a i (joinAssignments P s t i)) = (∏i : {i // P i},a i.val (s i))*
      (∏j : {i // ¬P i},a j.val (t j)) := by
  rw [←Fintype.prod_subtype_mul_prod_subtype P]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr (by ext;simp)
    intro i hi
    simp [joinAssignments,i.property]
  · apply Finset.prod_congr (by ext;simp)
    intro i hi
    simp [joinAssignments,i.property]

theorem injectiveTuplePolynomial_split (a : I→A→R) :
    injectiveTuplePolynomial a =
      ∑t : {i // ¬P i}→A,if Function.Injective t then
        (∏j : {i // ¬P i},a j.val (t j))*
          injectiveTuplePolynomial (fun i : {i // P i}=>fun p=>
            if ∀j : {i // ¬P i},p≠t j then a i.val p else 0)
      else 0 := by
  unfold injectiveTuplePolynomial
  rw [←(assignmentSplit (A:=A) P).symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr (by ext;simp)
  intro t ht
  by_cases hti : Function.Injective t
  · rw [ite_eq_left hti,Finset.mul_sum]
    apply Finset.sum_congr (by ext;simp)
    intro s hs
    change (if Function.Injective (joinAssignments P s t) then ∏i,a i (joinAssignments P s t i) else 0)=_
    simp only [joinAssignments_product,injective_joinAssignments]
    by_cases hsi : Function.Injective s
    · rw [ite_eq_left hsi,Fintype.prod_ite_zero]
      by_cases hc : ∀i : {i // P i},∀j : {i // ¬P i},s i≠t j
      · simp [hsi,hti,hc,mul_comm]
      · simp only [hsi,hti,hc,true_and,ite_false,mul_zero]
    · simp only [hsi,false_and,ite_false,mul_zero]
  · rw [ite_eq_right hti]
    apply Finset.sum_eq_zero
    intro s hs
    change (if Function.Injective (joinAssignments P s t) then _ else 0)=0
    simp [injective_joinAssignments,hti]

end
end OAI.SevenEighths.Deletion26
