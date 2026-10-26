/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Four-type geometry from an actual retained marked-squarefree coefficient.
Pools may overlap and repeat; no coefficient projection is claimed to contract
the completed row norm. Inclusion-exclusion supplies its later payment. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SourceModifier
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103CommonGeometry.ActualPair

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentRemainingBox CenteredMomentLiveSupport
open Record1252270103CommonGeometry CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def markedProduct (v : Tuple ι) : Ideal O := ∏i,v (Sum.inl i)

/-- K is the product of all already frozen marked factors, retained exactly. -/
def markedSourceModifier (A₁ A₂ D K : Ideal O) (F : Ideal O→ℂ) (v : Tuple ι) : ℂ :=
  squarefreeIndicator (K*markedProduct v)*sourceModifier A₁ A₂ D F v

theorem markedSourceModifier_nonzero (A₁ A₂ D K : Ideal O) (F : Ideal O→ℂ)
    (v : Tuple ι) (h : markedSourceModifier A₁ A₂ D K F v≠0) :
    Squarefree (markedProduct v) ∧ Squarefree (v (Sum.inr 0)*v (Sum.inr 1)) := by
  have hm : Squarefree (K*markedProduct v) := by
    by_contra hn
    exact h (by simp [markedSourceModifier,squarefreeIndicator,hn])
  have hs := (sourceModifier_nonzero A₁ A₂ D F v
    (mul_ne_zero_iff.mp h).2).2.1
  have he : A₁*v (Sum.inr 0)*A₂*v (Sum.inr 1)=
      (A₁*A₂)*(v (Sum.inr 0)*v (Sum.inr 1)) := by ring
  rw [he] at hs
  exact ⟨hm.of_mul_right,hs.of_mul_right⟩

theorem tuple_valuation_of_projectors (v : Tuple ι)
    (hm : Squarefree (markedProduct v))
    (hp : Squarefree (v (Sum.inr 0)*v (Sum.inr 1))) :
    ValuationAtMostTwo (finiteTupleProduct v) := by
  simpa only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,markedProduct]
    using two_squarefree_valuation_bound (markedProduct v) _ hm hp

/-- The two literal projectors in each surviving summand replace the old
pairwise-disjoint-pool hypothesis. This applies to arbitrary finite boxes. -/
theorem modified_column_valuation_bound (box : Finset (Tuple ι))
    (modifier coefficient : Tuple ι→ℂ)
    (hmod : ∀v∈box,modifier v≠0 →
      Squarefree (markedProduct v) ∧ Squarefree (v (Sum.inr 0)*v (Sum.inr 1)))
    (I : Ideal O)
    (hne : finiteColumnCoefficient box (fun v=>modifier v*coefficient v) I≠0) :
    ValuationAtMostTwo I := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  have hs := hmod v hv (mul_ne_zero_iff.mp hvn).1
  rw [←he]
  exact tuple_valuation_of_projectors v hs.1 hs.2

theorem marked_source_column_valuation_bound (box : Finset (Tuple ι))
    (A₁ A₂ D K : Ideal O) (F : Ideal O→ℂ) (coefficient : Tuple ι→ℂ)
    (I : Ideal O)
    (hne : finiteColumnCoefficient box
      (fun v=>markedSourceModifier A₁ A₂ D K F v*coefficient v) I≠0) :
    ValuationAtMostTwo I :=
  modified_column_valuation_bound box _ coefficient
    (fun v _=>markedSourceModifier_nonzero A₁ A₂ D K F v) I hne

theorem markedProduct_restore (B : Tuple ι) (v : Tuple (liveIndices B)) :
    markedProduct (restoreTuple B v)=markedProduct v := by
  unfold markedProduct
  simp only [restoreTuple,Sum.elim_inl]
  exact (Finset.prod_attach_eq_prod_dite (liveIndices B)
    (fun i=>v (Sum.inl i))).symm

theorem markedProduct_allocate (B : Tuple ι) (v : Tuple (liveIndices B)) :
    markedProduct (fun i=>B i*restoreTuple B v i)=markedProduct B*markedProduct v := by
  unfold markedProduct
  rw [Finset.prod_mul_distrib]
  change markedProduct B*markedProduct (restoreTuple B v)=_
  rw [markedProduct_restore]
  rfl

theorem markedSourceModifier_common_allocation (A₁ A₂ D K C : Ideal O)
    (F : Ideal O→ℂ) (B : Tuple ι) (hB : finiteTupleProduct B=C)
    (v : Tuple (liveIndices B)) :
    pulledModifier B (markedSourceModifier A₁ A₂ D K F) v=
      markedSourceModifier (A₁*B (Sum.inr 0)) (A₂*B (Sum.inr 1))
        (D*C) (K*markedProduct B) F v := by
  change squarefreeIndicator (K*markedProduct (fun i=>B i*restoreTuple B v i))*
    pulledModifier B (sourceModifier A₁ A₂ D F) v=_
  rw [markedProduct_allocate,sourceModifier_common_allocation A₁ A₂ D C F B hB v]
  simp only [markedSourceModifier,mul_assoc]

end
end OAI.SevenEighths.Record1252270103Source.Collision

#print axioms OAI.SevenEighths.Record1252270103Source.Collision.markedSourceModifier_nonzero
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.modified_column_valuation_bound
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.marked_source_column_valuation_bound
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.markedSourceModifier_common_allocation
