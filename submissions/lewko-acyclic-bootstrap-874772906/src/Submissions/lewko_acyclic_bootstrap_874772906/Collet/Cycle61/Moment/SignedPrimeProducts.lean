import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.SignedSourceDictionary

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstColumns
local notation "O" => HeckeFamily.O

theorem numerator_product {ι : Type*} (S : Finset ι) (p : ι → O)
    (n : O) (hn : Supported (Ideal.span {n})) :
    idealRowHom (∏ i ∈ S, p i) (Ideal.span {n}) =
      ∏ i ∈ S, idealRowHom (p i) (Ideal.span {n}) :=
  map_prod (movingNumeratorRow n hn) _ _

/-- The complete left column is encoded before taking absolute values. -/
theorem left_column_signed_product {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (e n : O)
    (hp : ∀ i ∈ S, Supported (Ideal.span {p i}))
    (hn : Supported (Ideal.span {n}))
    (hpp : ∀ i ∈ S, goodLambda^2 ∣ p i - 1) (hnp : goodLambda^2 ∣ n - 1) :
    leftCoefficient e (∏ i ∈ S, p i)
      (fun x => ∏ i ∈ S, idealRowHom x (Ideal.span {p i})^(t i)) n =
      (∏ i ∈ S, sexticReciprocityPhase (p i) n^(t i)) *
        idealRowHom (e * ∏ i ∈ S, (p i)^(1+t i)) (Ideal.span {n}) := by
  unfold leftCoefficient
  rw [idealRowHom_argument_mul, numerator_product S p n hn]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  have he := Finset.prod_congr rfl (fun i hi =>
    LocalMomentSignedRows.left_local (p i) n (t i) (hp i hi) hn (hpp i hi) hnp)
  rw [he, Finset.prod_mul_distrib, ← numerator_product S (fun i => (p i)^(1+t i)) n hn,
    idealRowHom_argument_mul]
  ring

/-- The complete right column uses positive representatives `7-t`, retaining
the nonunit zero even when the active exponent cancels modulo six. -/
theorem right_column_signed_product {ι : Type*} (S : Finset ι)
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (t : ι → ℕ) (e n : O)
    (ht : ∀ i ∈ S, 0 < t i) (ht6 : ∀ i ∈ S, t i < 6)
    (hg : ∀ i ∈ S, goodLambda ∉ Ideal.span {p i})
    (hc : ∀ i ∈ S, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hp : ∀ i ∈ S, Supported (Ideal.span {p i}))
    (hn : Supported (Ideal.span {n}))
    (hpp : ∀ i ∈ S, goodLambda^2 ∣ p i - 1) (hnp : goodLambda^2 ∣ n - 1) :
    rightCoefficient e (∏ i ∈ S, p i)
      (fun x => ∏ i ∈ S, idealRowHom x (Ideal.span {p i})^(t i)) n =
      (∏ i ∈ S, sexticReciprocityPhase (p i) n^(6-t i)) *
        idealRowHom (e * ∏ i ∈ S, (p i)^(7-t i)) (Ideal.span {n}) := by
  unfold rightCoefficient
  rw [idealRowHom_argument_mul, numerator_product S p n hn, star_prod]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  have he := Finset.prod_congr rfl (fun i hi =>
    LocalMomentSignedRows.right_local (p i) n (t i) (ht i hi) (ht6 i hi)
      (hg i hi) (hc i hi) (hp i hi) hn (hpp i hi) hnp)
  rw [he, Finset.prod_mul_distrib, ← numerator_product S (fun i => (p i)^(7-t i)) n hn,
    idealRowHom_argument_mul]
  ring

/-- Cancelled residues become the exact original Euler holes, never exponent
zero at a nonunit. The remaining numerator uses the uncancelled prime powers. -/
theorem sixth_product_retains_holes {ι : Type*} (S : Finset ι)
    (p : ι → O) (t : ι → ℕ) (n : O) (hn : Supported (Ideal.span {n})) :
    idealRowHom (∏ i ∈ S, (p i)^(t i)) (Ideal.span {n}) =
      (∏ i ∈ S.filter (fun i => t i = 6),
        if IsCoprime n (p i) then (1:ℂ) else 0) *
      idealRowHom (∏ i ∈ S.filter (fun i => t i ≠ 6), (p i)^(t i))
        (Ideal.span {n}) := by
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => t i = 6)
    (fun i => (p i)^(t i)), idealRowHom_argument_mul]
  congr 1
  rw [numerator_product _ _ n hn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2, idealRowHom_sixth_mask _ _ hn,
    Ideal.isCoprime_span_singleton_iff]

#print axioms left_column_signed_product
#print axioms right_column_signed_product
#print axioms sixth_product_retains_holes
end
end OAI.SevenEighths.Cycle61Moment
