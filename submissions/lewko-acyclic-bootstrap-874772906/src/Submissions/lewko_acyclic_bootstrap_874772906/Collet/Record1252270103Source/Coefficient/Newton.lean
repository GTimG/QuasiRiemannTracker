/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact finite Newton coefficients of the corrected whole-pool amplifier. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.PoolPayment
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators

def newtonDenominator (P r : ℝ) (j : ℕ) : ℝ :=
  ∏i∈Finset.range (j+1),(P-r-(i:ℝ))

def newtonCoefficient (P r : ℝ) (j : ℕ) : ℝ :=
  P*(j.factorial:ℝ)/newtonDenominator P r j

theorem newtonDenominator_pos (P r : ℝ) (j : ℕ) (h : r+j<P) :
    0<newtonDenominator P r j := by
  apply Finset.prod_pos
  intro i hi
  have hi' : (i:ℝ)≤j := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  linarith

theorem newtonDenominator_succ (P r : ℝ) (j : ℕ) :
    newtonDenominator P r (j+1)=newtonDenominator P r j*(P-r-(j+1:ℕ)) := by
  exact Finset.prod_range_succ _ _

theorem newtonDenominator_shift (P r : ℝ) (j : ℕ) :
    newtonDenominator P r (j+1)=(P-r)*newtonDenominator P (r+1) j := by
  unfold newtonDenominator
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero,sub_zero]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  push_cast
  ring

theorem newtonCoefficient_difference (P r : ℝ) (j : ℕ) (h : r+(j+1:ℕ)<P) :
    newtonCoefficient P (r+1) j-newtonCoefficient P r j=newtonCoefficient P r (j+1) := by
  have hj : r+j<P := by push_cast at h;linarith
  have hs : r+1+j<P := by push_cast at h;linarith
  have hp : P-r≠0 := by push_cast at h;linarith
  have he : P-r-(j+1:ℕ)≠0 := by linarith
  have hd := (newtonDenominator_pos P r j hj).ne'
  have hd' := (newtonDenominator_pos P (r+1) j hs).ne'
  have hl : P*(j.factorial:ℝ)/newtonDenominator P (r+1) j=
      (P*(j.factorial:ℝ)*(P-r))/newtonDenominator P r (j+1) := by
    rw [newtonDenominator_shift]
    field_simp
  have hr : P*(j.factorial:ℝ)/newtonDenominator P r j=
      (P*(j.factorial:ℝ)*(P-r-(j+1:ℕ)))/newtonDenominator P r (j+1) := by
    rw [newtonDenominator_succ]
    field_simp
  unfold newtonCoefficient
  rw [hl,hr,←sub_div,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  congr 1
  ring

theorem pool_correction_forward_difference (P r : ℝ) (j : ℕ) (x : ℝ)
    (h : r+x+j<P) :
    ((fwdDiff (1:ℝ))^[j] (fun y : ℝ=>P/(P-r-y))) x=newtonCoefficient P (r+x) j := by
  induction j generalizing x with
  | zero => simp [newtonCoefficient,newtonDenominator,sub_add_eq_sub_sub]
  | succ j ih =>
    rw [Function.iterate_succ_apply',fwdDiff]
    have hx : r+x+j<P := by push_cast at h;linarith
    have hx' : r+(x+1)+j<P := by push_cast at h;linarith
    rw [ih (x+1) hx',ih x hx]
    rw [show r+(x+1)=r+x+1 by ring]
    exact newtonCoefficient_difference P (r+x) j h

/-- Shifted CA8. The coefficient is a finite polynomial on the entire
nonnegative count domain; equality is asserted only before its first pole. -/
theorem corrected_pool_newton (P r : ℝ) (n : ℕ) (h : r+n<P) :
    P/(P-r-n)=∑j∈Finset.range (n+1),(n.choose j:ℝ)*newtonCoefficient P r j := by
  have hn := shift_eq_sum_fwdDiff_iter (1:ℝ) (fun y : ℝ=>P/(P-r-y)) n 0
  simp only [nsmul_eq_mul,mul_one,zero_add] at hn
  rw [hn]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : (j:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjP : r+0+j<P := by linarith
  rw [pool_correction_forward_difference P r j 0 hjP,add_zero]

theorem corrected_pool_newton_powerset {ι : Type*} (D : Finset ι)
    (P r : ℝ) (h : r+D.card<P) :
    P/(P-r-D.card)=∑S∈D.powerset,newtonCoefficient P r S.card := by
  rw [Finset.sum_powerset]
  simp only [Finset.sum_powersetCard,nsmul_eq_mul]
  exact corrected_pool_newton P r D.card h

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.corrected_pool_newton
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_pool_newton_powerset
