/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Uniform finite mass of the exact amplifier correction. A deliberately loose
fixed-depth constant suffices; no prime-size asymptotic is substituted. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.Newton
import Mathlib.Data.Nat.Choose.Bounds

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators

theorem newtonCoefficient_nonneg (P r : ℝ) (j : ℕ) (hP : 0≤P) (h : r+j<P) :
    0≤newtonCoefficient P r j :=
  div_nonneg (mul_nonneg hP (Nat.cast_nonneg _)) (newtonDenominator_pos P r j h).le

theorem newtonCoefficient_bound (P r : ℝ) (j : ℕ) (hP : 0<P)
    (hbudget : 2*(r+j+1)≤P) :
    newtonCoefficient P r j≤2^(j+1)*(j.factorial:ℝ)/P^j := by
  have hhalf : 0<P/2 := half_pos hP
  have hden : (P/2)^(j+1)≤newtonDenominator P r j := by
    unfold newtonDenominator
    calc
      _ = ∏i∈Finset.range (j+1),(P/2) := by simp only [Finset.prod_const,Finset.card_range]
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun _ _=>hhalf.le)
        intro i hi
        have hi' : (i:ℝ)≤j := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        linarith
  unfold newtonCoefficient
  apply (div_le_div_of_nonneg_left (mul_nonneg hP.le (Nat.cast_nonneg _))
    (pow_pos hhalf _) hden).trans_eq
  rw [div_pow,pow_succ]
  field_simp

def newtonMassBound (R : ℕ) : ℝ :=
  ∑j∈Finset.range (R+1),2^(j+1)*(j.factorial:ℝ)*2^j

theorem newton_level_mass {ι : Type*} (pool : Finset ι) (r : ℝ) (j : ℕ)
    (hP : 0<pool.card) (hbudget : 2*(r+j+1)≤pool.card) :
    (∑S∈pool.powersetCard j,newtonCoefficient pool.card r S.card*2^S.card)≤
      2^(j+1)*(j.factorial:ℝ)*2^j := by
  have hP' : (0:ℝ)<pool.card := Nat.cast_pos.mpr hP
  have hcoeff := newtonCoefficient_bound pool.card r j hP' hbudget
  have hcoeff0 : 0≤newtonCoefficient pool.card r j :=
    newtonCoefficient_nonneg pool.card r j hP'.le (by linarith)
  have hchoose : (pool.card.choose j:ℝ)≤(pool.card:ℝ)^j := by
    exact_mod_cast Nat.choose_le_pow pool.card j
  rw [Finset.sum_powersetCard j pool (fun k=>newtonCoefficient pool.card r k*2^k),nsmul_eq_mul]
  calc
    _ ≤ (pool.card:ℝ)^j*(2^(j+1)*(j.factorial:ℝ)/(pool.card:ℝ)^j*2^j) := by
      gcongr
    _ = _ := by field_simp

/-- All subset choices and both ordinary-factor allocations have bounded
total coefficient mass at every fixed depth, uniformly in the whole pool. -/
theorem newton_total_mass {ι : Type*} (pool : Finset ι) (r : ℝ) (R : ℕ)
    (hP : 0<pool.card) (hbudget : 2*(r+R+1)≤pool.card) :
    (∑j∈Finset.range (R+1),∑S∈pool.powersetCard j,
      newtonCoefficient pool.card r S.card*2^S.card)≤newtonMassBound R := by
  apply Finset.sum_le_sum
  intro j hj
  have hj' : (j:ℝ)≤R := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  exact newton_level_mass pool r j hP (by linarith)

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.newtonCoefficient_bound
#print axioms OAI.SevenEighths.Record1252270103Source.newton_total_mass
