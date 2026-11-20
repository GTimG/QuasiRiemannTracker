/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterSeries

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators

/-- H9 convolved with the two ordinary geometric series. -/
def goodLocalStep (a b : ℕ) (j : Fin 7) : ℂ :=
  if (h3Exponent j).1 ≤ a ∧ (h3Exponent j).2 ≤ b then h3Sign j else 0

lemma goodLocalStep_sum (a b : ℕ) :
    1 + ∑ j : Fin 7,goodLocalStep a b j = if a+b ≤ 2 then 1 else 0 := by
  unfold goodLocalStep
  norm_num [h3Exponent,h3Sign,Fin.sum_univ_succ]
  split_ifs <;> norm_num at * <;> omega

lemma goodLocalTerm_factor (c d : ℂ) (a b : ℕ) (j : Fin 7) :
    (if (h3Exponent j).1 ≤ a ∧ (h3Exponent j).2 ≤ b then
      h3Term c d j*c^(a-(h3Exponent j).1)*d^(b-(h3Exponent j).2) else 0) =
      goodLocalStep a b j*(c^a*d^b) := by
  unfold goodLocalStep h3Term
  split_ifs with h
  · have ha : (h3Exponent j).1+(a-(h3Exponent j).1)=a := Nat.add_sub_of_le h.1
    have hb : (h3Exponent j).2+(b-(h3Exponent j).2)=b := Nat.add_sub_of_le h.2
    calc
      _ = h3Sign j*(c^((h3Exponent j).1+(a-(h3Exponent j).1))*
          d^((h3Exponent j).2+(b-(h3Exponent j).2))) := by simp only [pow_add]; ring
      _ = _ := by rw [ha,hb]
  · simp

/-- The coupled cutoff includes the shared-prime case (1,1), without
any nonvanishing assumption on either character value. -/
theorem goodLocal_convolution (c d : ℂ) (a b : ℕ) :
    c^a*d^b + ∑ j : Fin 7,
      (if (h3Exponent j).1 ≤ a ∧ (h3Exponent j).2 ≤ b then
        h3Term c d j*c^(a-(h3Exponent j).1)*d^(b-(h3Exponent j).2) else 0) =
      if a+b ≤ 2 then c^a*d^b else 0 := by
  simp_rw [goodLocalTerm_factor]
  rw [←Finset.sum_mul,←one_add_mul,goodLocalStep_sum]
  split_ifs <;> simp

#print axioms goodLocalStep_sum
#print axioms goodLocal_convolution
end
end QRH.Cycle092.SignedCenter
