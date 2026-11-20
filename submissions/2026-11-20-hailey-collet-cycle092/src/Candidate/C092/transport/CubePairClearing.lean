/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairLocal
import Candidate.C092.transport.SignedCenterClearing

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators

/-- Finite Euler deletion cancels both geometric series even at a zero
character value. -/
theorem deletionLocal_convolution (c d : ℂ) (a b : ℕ) :
    (∑ j : Fin 4, if deletionExponent₁ j ≤ a ∧ deletionExponent₂ j ≤ b then
      deletionTerm c d j*c^(a-deletionExponent₁ j)*d^(b-deletionExponent₂ j) else 0) =
      if a=0 ∧ b=0 then 1 else 0 := by
  cases a with
  | zero =>
    cases b with
    | zero => norm_num [deletionTerm,deletionExponent₁,deletionExponent₂,Fin.sum_univ_succ]
    | succ b =>
      simp [deletionTerm,deletionExponent₁,deletionExponent₂,Fin.sum_univ_succ,pow_succ]
      ring
  | succ a =>
    cases b with
    | zero =>
      simp [deletionTerm,deletionExponent₁,deletionExponent₂,Fin.sum_univ_succ,pow_succ]
      ring
    | succ b =>
      simp [deletionTerm,deletionExponent₁,deletionExponent₂,Fin.sum_univ_succ,pow_succ]
      ring

/-- The cancellation is an offset delta kernel, not division by an Euler
factor or by a character value. -/
theorem deletionLocal_offset (c d : ℂ) (a b i l : ℕ) :
    (∑ j : Fin 4, if i+deletionExponent₁ j ≤ a ∧ l+deletionExponent₂ j ≤ b then
      deletionTerm c d j*c^(a-i-deletionExponent₁ j)*d^(b-l-deletionExponent₂ j) else 0) =
      if a=i ∧ b=l then 1 else 0 := by
  by_cases hi : i ≤ a
  · by_cases hl : l ≤ b
    · have hg (j : Fin 4) :
          (i+deletionExponent₁ j ≤ a ∧ l+deletionExponent₂ j ≤ b) ↔
          (deletionExponent₁ j ≤ a-i ∧ deletionExponent₂ j ≤ b-l) := by omega
      simp_rw [hg]
      rw [deletionLocal_convolution]
      have he : (a-i=0 ∧ b-l=0) ↔ (a=i ∧ b=l) := by omega
      simp only [he]
    · have hg (j : Fin 4) : ¬(i+deletionExponent₁ j ≤ a ∧ l+deletionExponent₂ j ≤ b) := by omega
      simp only [ite_eq_right (hg _),Finset.sum_const_zero]
      rw [ite_eq_right (by omega)]
  · have hg (j : Fin 4) : ¬(i+deletionExponent₁ j ≤ a ∧ l+deletionExponent₂ j ≤ b) := by omega
    simp only [ite_eq_right (hg _),Finset.sum_const_zero]
    rw [ite_eq_right (by omega)]

/-- Convolve the actual finite residual polynomial with the authentic
ordinary characters and their deletion numerator. -/
theorem exceptionalLocal_convolution (c d u v : ℂ) (a b : ℕ) (allowed : Finset (ℕ×ℕ)) :
    (∑ q ∈ allowed, ∑ j : Fin 4,
      if q.1+deletionExponent₁ j ≤ a ∧ q.2+deletionExponent₂ j ≤ b then
        (u^q.1*v^q.2)*deletionTerm c d j*
          c^(a-q.1-deletionExponent₁ j)*d^(b-q.2-deletionExponent₂ j) else 0) =
      if (a,b) ∈ allowed then u^a*v^b else 0 := by
  have hterm (q : ℕ×ℕ) :
      (∑ j : Fin 4,
        if q.1+deletionExponent₁ j ≤ a ∧ q.2+deletionExponent₂ j ≤ b then
          (u^q.1*v^q.2)*deletionTerm c d j*
            c^(a-q.1-deletionExponent₁ j)*d^(b-q.2-deletionExponent₂ j) else 0) =
        if (a,b)=q then u^q.1*v^q.2 else 0 := by
    calc
      _ = (u^q.1*v^q.2)*(∑ j : Fin 4,
          if q.1+deletionExponent₁ j ≤ a ∧ q.2+deletionExponent₂ j ≤ b then
            deletionTerm c d j*c^(a-q.1-deletionExponent₁ j)*d^(b-q.2-deletionExponent₂ j) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = _ := by
        rw [deletionLocal_offset]
        by_cases h : a=q.1 ∧ b=q.2
        · have hq : (a,b)=q := Prod.ext h.1 h.2
          simp [h]
        · have hq : (a,b)≠q := by intro he; exact h ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
          simp [h,hq]
  simp_rw [hterm]
  by_cases h : (a,b) ∈ allowed
  · rw [ite_eq_left h,Finset.sum_eq_single (a,b)]
    · simp
    · intro q _ hq
      simp [Ne.symm hq]
    · exact fun hn => False.elim (hn h)
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro q hq
    rw [ite_eq_right (by intro he; exact h (he.symm ▸ hq))]

#print axioms deletionLocal_offset
#print axioms exceptionalLocal_convolution
end
end QRH.Cycle092.SignedCenter
