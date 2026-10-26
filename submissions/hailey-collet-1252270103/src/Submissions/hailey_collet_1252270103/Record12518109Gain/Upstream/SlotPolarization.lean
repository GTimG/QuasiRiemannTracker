/- Adapted from PR63 gao-balanced-marked-20261017; Apache-2.0. Exact source provenance is in evidence/homogeneous-gain/upstream-provenance.json. -/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI.SevenEighths.Cycle61MarkedHeight
noncomputable section
open scoped Classical BigOperators
open Polynomial

/-- Fixed coefficients that extract the first coefficient of a polynomial
of degree at most `N` from its values at `0,...,N`. -/
def derivativeWeight (N : ℕ) (j : Fin (N+1)) : ℂ :=
  (Lagrange.basis Finset.univ (fun k : Fin (N+1)=>(k.val:ℂ)) j).coeff 1

theorem coefficient_one_interpolation (N : ℕ) (p : Polynomial ℂ)
    (hp : p.natDegree≤N) :
    p.coeff 1 = ∑j : Fin (N+1),derivativeWeight N j*p.eval (j.val:ℂ) := by
  have hi : Set.InjOn (fun k : Fin (N+1)=>(k.val:ℂ)) (Finset.univ : Finset (Fin (N+1))) := by
    intro a _ b _ h
    apply Fin.ext
    change (a.val:ℂ)=(b.val:ℂ) at h
    exact_mod_cast h
  have hd : p.degree<(Finset.univ : Finset (Fin (N+1))).card := by
    apply lt_of_le_of_lt degree_le_natDegree
    simp only [Finset.card_univ,Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hp
  have he := congrArg (fun q : Polynomial ℂ=>q.coeff 1) (Lagrange.eq_interpolate hi hd)
  simpa only [Lagrange.interpolate_apply,finsetSum_coeff,coeff_C_mul,derivativeWeight,
    mul_comm] using he

/-- Differentiating a product of slots is a finite linear combination of
products with one common profile `A + j B`. The interpolation constants
are independent of the rows, scales, and coefficients. -/
theorem first_product_polarization {Slot : Type*} [DecidableEq Slot]
    (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N) (A B : Slot→ℂ) :
    (∑s∈slots,(∏k∈slots.erase s,A k)*B s) =
      ∑j : Fin (N+1),derivativeWeight N j*(∏s∈slots,(A s+(j.val:ℂ)*B s)) := by
  let p : Polynomial ℂ := ∏s∈slots,(C (B s)*X+C (A s))
  have hd : p.natDegree≤N := by
    have hs : (∑s∈slots,(C (B s)*X+C (A s) : Polynomial ℂ).natDegree) ≤ slots.card := by
      calc
        (∑s∈slots,(C (B s)*X+C (A s) : Polynomial ℂ).natDegree) ≤
            ∑s∈slots,(1 : ℕ) := by
          apply Finset.sum_le_sum
          intro s hs
          exact natDegree_linear_le
        _ = slots.card := by simp
    exact (natDegree_prod_le slots (fun s=>(C (B s)*X+C (A s) : Polynomial ℂ))).trans
      (hs.trans hN)
  have hc : p.coeff 1=∑s∈slots,(∏k∈slots.erase s,A k)*B s := by
    have he := congrArg (fun q : Polynomial ℂ=>q.eval 0)
      (derivative_prod_finset (s:=slots) (f:=fun s=>C (B s)*X+C (A s)))
    rw [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] at he
    simpa [p,Polynomial.eval_finsetSum,Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_add] using he
  rw [←hc,coefficient_one_interpolation N p hd]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [p,Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro s _
  ring

/-- A single energy estimate for finitely many common profiles controls
all first height derivatives; no estimate for independently varying slot
profiles is required. -/
theorem polarized_product_energy {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N)
    (A B : Row→Slot→ℂ) (C : Row→ℂ) (E : ℝ)
    (henergy : ∀j : Fin (N+1),
      ∑u∈rows,‖C u*(∏s∈slots,(A u s+(j.val:ℂ)*B u s))‖^2≤E) :
    (∑u∈rows,‖C u*(∑s∈slots,(∏k∈slots.erase s,A u k)*B u s)‖^2)≤
      ((∑j : Fin (N+1),‖derivativeWeight N j‖^2)*(N+1))*E := by
  have each (u : Row) :
      ‖C u*(∑s∈slots,(∏k∈slots.erase s,A u k)*B u s)‖^2≤
      (∑j : Fin (N+1),‖derivativeWeight N j‖^2)*
        ∑j : Fin (N+1),‖C u*(∏s∈slots,(A u s+(j.val:ℂ)*B u s))‖^2 := by
    rw [first_product_polarization slots N hN]
    have he : C u*(∑j : Fin (N+1),derivativeWeight N j*
        (∏s∈slots,(A u s+(j.val:ℂ)*B u s))) =
      ∑j : Fin (N+1),derivativeWeight N j*
        (C u*(∏s∈slots,(A u s+(j.val:ℂ)*B u s))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro _ _
      ring
    rw [he]
    apply le_trans ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr
      (norm_sum_le _ _)) ?_
    simp_rw [norm_mul]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  apply (Finset.sum_le_sum (fun u _=>each u)).trans
  rw [←Finset.mul_sum,Finset.sum_comm]
  have hs := Finset.sum_le_sum (fun j (_:j∈(Finset.univ : Finset (Fin (N+1))))=>henergy j)
  have hw : 0≤∑j : Fin (N+1),‖derivativeWeight N j‖^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,mul_assoc] using mul_le_mul_of_nonneg_left hs hw

end
end OAI.SevenEighths.Cycle61MarkedHeight
#print axioms OAI.SevenEighths.Cycle61MarkedHeight.first_product_polarization
#print axioms OAI.SevenEighths.Cycle61MarkedHeight.polarized_product_energy
