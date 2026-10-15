import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrimeConstants
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationShortening
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSourceMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.LocalMomentSignedRows
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSupportedCorrelation CenteredMomentFirstColumns
open CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O
set_option autoImplicit false

/-- Reciprocity fixes the sign: the left coefficient uses exponent 1+t. -/
theorem left_local (p n : O) (t : ℕ)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * idealRowHom n (Ideal.span {p})^t =
      sexticReciprocityPhase p n^t * idealRowHom (p^(1+t)) (Ideal.span {n}) := by
  rw [idealRowHom_primary_reciprocity p n hpp hnp hp hn, mul_pow,
      idealRowHom_argument_pow p (1+t) _ hn, pow_add, pow_one]
  ring

/-- A sixth power retains its original puncture, including on nonunits. -/
theorem left_canceled (p n : O)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * idealRowHom n (Ideal.span {p})^5 =
      sexticReciprocityPhase p n^5 *
        (if IsCoprime n p then (1:ℂ) else 0) := by
  rw [left_local p n 5 hp hn hpp hnp]
  norm_num only
  rw [idealRowHom_sixth_mask _ _ hn, Ideal.isCoprime_span_singleton_iff]

/-- Conjugation reverses the first active exponent. The raw representative
7-t is positive, so the nonunit zero is never replaced by 0^0. -/
theorem right_local (p n : O) [(Ideal.span {p}).IsMaximal] (t : ℕ)
    (ht : 0<t) (ht6 : t<6)
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * star (idealRowHom n (Ideal.span {p})^t) =
      sexticReciprocityPhase p n^(6-t) * idealRowHom (p^(7-t)) (Ideal.span {n}) := by
  let χ := ActualEisensteinCubic.canonicalSextic (Ideal.span {p}) hg
  have hinv : (χ^t)⁻¹=χ^(6-t) := by
    apply inv_eq_of_mul_eq_one_right
    rw [←pow_add,Nat.add_sub_of_le ht6.le]
    exact ProbePrimePower.actualSextic_six _ hg hc
  have hs : star (idealRowHom n (Ideal.span {p})^t) =
      idealRowHom n (Ideal.span {p})^(6-t) := by
    rw [idealRowHom_prime n _ hg]
    change star (χ (Ideal.Quotient.mk _ n)^t)=χ (Ideal.Quotient.mk _ n)^(6-t)
    rw [←MulChar.pow_apply' χ (by omega : t≠0),MulChar.star_apply',hinv,
      MulChar.pow_apply' χ (by omega : 6-t≠0)]
  rw [hs,left_local p n (6-t) hp hn hpp hnp]
  rw [show 1+(6-t)=7-t by omega]

/-- At t=1 the right coefficient is exactly a puncture, not one. -/
theorem right_canceled (p n : O) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * star (idealRowHom n (Ideal.span {p})) =
      sexticReciprocityPhase p n^5 *
        (if IsCoprime n p then (1:ℂ) else 0) := by
  have h := right_local p n 1 (by decide) (by decide) hg hc hp hn hpp hnp
  norm_num only [pow_one] at h
  rw [h,idealRowHom_sixth_mask _ _ hn,Ideal.isCoprime_span_singleton_iff]

/-- Multiplying all already retained row numerators is literal, before
reducing any sixth powers and before taking absolute values. -/
theorem effective_row (e F G V h : O) (I : Ideal O) :
    idealRowHom (e*F) I * idealRowHom ((G*V)*h) I =
      idealRowHom ((e*F)*(G*V)*h) I := by
  simp only [idealRowHom_argument_mul]
  ring

#print axioms left_local
#print axioms left_canceled
#print axioms right_local
#print axioms right_canceled
#print axioms effective_row
end SevenEighths.LocalMomentSignedRows
end
end OAI
