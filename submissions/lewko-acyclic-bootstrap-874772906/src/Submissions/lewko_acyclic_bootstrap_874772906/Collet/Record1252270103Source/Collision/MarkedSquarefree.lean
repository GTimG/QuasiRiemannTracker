/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The injective tuple projector is precisely the marked-squarefree projector.
Frozen marked factors split off only with the actual coprimality premise. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.Projector
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.InclusionExclusion

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal Record1252270103CommonGeometry
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
local notation "O" => ActualEisensteinCubic.O

theorem prime_product_squarefree_iff_injective {ι : Type*} [Fintype ι]
    (p : ι→Ideal O) (hp : ∀i,Prime (p i)) :
    Squarefree (∏i,p i) ↔ Function.Injective p := by
  constructor
  · intro hs i j hij
    by_contra hn
    have hd := Finset.prod_dvd_prod_of_subset ({i,j}:Finset ι) Finset.univ p
      (Finset.subset_univ _)
    have hd' : p i*p i∣∏k,p k := by simpa [Finset.prod_pair hn,hij] using hd
    exact (hp i).not_isUnit (hs (p i) hd')
  · intro hinj
    exact marked_product_squarefree (fun i=>{p i}) p
      (fun i P hP=>by simpa only [Finset.mem_singleton.mp hP] using hp i)
      (fun i j hij=>Finset.disjoint_singleton.mpr (fun hh=>hij (hinj hh)))
      (fun i=>Finset.mem_singleton_self _)

theorem squarefreeIndicator_mul_of_coprime (K M : Ideal O) (h : IsCoprime K M) :
    squarefreeIndicator (K*M)=squarefreeIndicator K*squarefreeIndicator M := by
  by_cases hK : Squarefree K
  · by_cases hM : Squarefree M
    · have hm := squarefree_mul_iff.mpr ⟨h.isRelPrime,hK,hM⟩
      simp [squarefreeIndicator,hK,hM,hm]
    · have hm : ¬Squarefree (K*M) := fun hh=>hM hh.of_mul_right
      simp [squarefreeIndicator,hM,hm]
  · have hm : ¬Squarefree (K*M) := fun hh=>hK hh.of_mul_left
    simp [squarefreeIndicator,hK,hm]

theorem markedSourceModifier_split_frozen {ι : Type*} [Fintype ι]
    (A₁ A₂ D K : Ideal O) (F : Ideal O→ℂ) (v : CenteredMomentAddedZeroUniform.Tuple ι)
    (h : IsCoprime K (markedProduct v)) :
    markedSourceModifier A₁ A₂ D K F v=
      squarefreeIndicator K*markedSourceModifier A₁ A₂ D 1 F v := by
  unfold markedSourceModifier
  rw [squarefreeIndicator_mul_of_coprime K _ h]
  simp only [one_mul,mul_assoc]

/-- Ideal-indexed tuples on a prime atoms type: no disjointness assumption. -/
theorem injective_polynomial_eq_squarefree {ι : Type*} [Fintype ι]
    (atoms : Finset (Ideal O)) (hp : ∀P∈atoms,Prime P) (a : ι→atoms→ℂ) :
    injectiveTuplePolynomial a=
      ∑v : ι→atoms,squarefreeIndicator (∏i,(v i:Ideal O))*∏i,a i (v i) := by
  unfold injectiveTuplePolynomial
  apply Finset.sum_congr rfl
  intro v hv
  have he : Function.Injective (fun i=>(v i:Ideal O)) ↔ Function.Injective v := by
    constructor
    · intro h i j hij
      exact h (congrArg Subtype.val hij)
    · intro h i j hij
      exact h (Subtype.ext hij)
  have hs := (prime_product_squarefree_iff_injective (fun i=>(v i:Ideal O))
    (fun i=>hp (v i) (v i).property)).trans he
  by_cases hh : Function.Injective v
  · simp [squarefreeIndicator,hh,hs.mpr hh]
  · simp [squarefreeIndicator,hh,not_congr hs|>.mpr hh]

end
end OAI.SevenEighths.Record1252270103Source.Collision

#print axioms OAI.SevenEighths.Record1252270103Source.Collision.prime_product_squarefree_iff_injective
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.squarefreeIndicator_mul_of_coprime
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.markedSourceModifier_split_frozen
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.injective_polynomial_eq_squarefree
