/- Copyright (c) 2026 Sil. Apache-2.0.
The literal forward ordinary kernel and its anisotropic absolute mass.
The exponents 2/3 and 1/3 include the critical reflected length ratio.
-/
import Candidate.FourthPower.SieveCentralReference
import Candidate.FourthPower.LocalKernels

set_option autoImplicit false
namespace Candidate.FourthPower.KernelForwardMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open SieveDescent
local notation "Id" => Ideal ActualEisensteinCubic.O

def ordinaryExponent : Fin 12 → ℕ × ℕ :=
  ![(0,0),(0,5),(1,4),(2,3),(3,2),(4,1),(5,0),(1,5),(2,4),(3,3),(4,2),(5,1)]

def ordinaryCoefficient : Fin 12 → ℤ := ![1,-1,-1,-1,-1,-1,-1,1,1,1,1,1]

theorem critical_ordinary_weight (p : ℝ) (hp : 0 < p) (j k : ℕ) :
    p^(-(((j : ℝ)+k)/2))*p^(((k : ℝ)-j)/6) =
      p^(-((2*(j : ℝ)+k)/3)) := by
  rw [← Real.rpow_add hp]
  congr 1
  ring

theorem ordinary_exact (x y : ℂ) :
    LocalKernels.ordinary x y = ∑ i : Fin 12,
      (ordinaryCoefficient i : ℂ)*x^(ordinaryExponent i).1*y^(ordinaryExponent i).2 := by
  rw [LocalKernels.ordinary_expansion]
  norm_num [ordinaryExponent,ordinaryCoefficient,Fin.sum_univ_succ]
  ring

def ordinaryWeight (p : ℝ) (i : Fin 12) : ℝ :=
  |(ordinaryCoefficient i : ℝ)| * p^(-((2*(ordinaryExponent i).1+(ordinaryExponent i).2 : ℝ)/3))

theorem ordinaryWeight_nonneg (p : ℝ) (hp : 0 ≤ p) (i : Fin 12) : 0 ≤ ordinaryWeight p i := by
  unfold ordinaryWeight
  positivity

theorem ordinaryWeight_zero (p : ℝ) : ordinaryWeight p 0 = 1 := by
  norm_num [ordinaryWeight,ordinaryCoefficient,ordinaryExponent]

theorem ordinary_term_bound (p : ℝ) (hp : 0 < p) (x y : ℂ)
    (hx : ‖x‖ ≤ p^(-(2/3 : ℝ))) (hy : ‖y‖ ≤ p^(-(1/3 : ℝ))) (i : Fin 12) :
    ‖(ordinaryCoefficient i : ℂ)*x^(ordinaryExponent i).1*y^(ordinaryExponent i).2‖ ≤
      ordinaryWeight p i := by
  have he : (p^(-(2/3 : ℝ)))^(ordinaryExponent i).1 *
      (p^(-(1/3 : ℝ)))^(ordinaryExponent i).2 =
      p^(-((2*(ordinaryExponent i).1+(ordinaryExponent i).2 : ℝ)/3)) := by
    simp only [← Real.rpow_natCast,← Real.rpow_mul hp.le,← Real.rpow_add hp]
    congr 1
    ring
  simp only [norm_mul,norm_pow,Complex.norm_intCast]
  rw [mul_assoc,ordinaryWeight,← he]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _)
      (pow_le_pow_left₀ (norm_nonneg _) hy _) (by positivity) (by positivity)) (abs_nonneg _)

theorem ordinaryWeight_nonconstant (p : ℝ) (hp : 1 ≤ p) (i : Fin 12) (hi : i ≠ 0) :
    ordinaryWeight p i ≤ p^(-(5/3 : ℝ)) := by
  have hc : |(ordinaryCoefficient i : ℝ)| = 1 := by fin_cases i <;> norm_num [ordinaryCoefficient]
  have he : (5 : ℝ) ≤ 2*(ordinaryExponent i).1+(ordinaryExponent i).2 := by
    fin_cases i <;> norm_num [ordinaryExponent] at *
  rw [ordinaryWeight,hc,one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hp (by linarith)

theorem ordinary_local_mass (p : ℝ) (hp : 1 ≤ p) :
    (∑ i : Fin 12, ordinaryWeight p i) ≤ 1+11*p^(-(5/3 : ℝ)) := by
  have hh : (∑ i ∈ (Finset.univ : Finset (Fin 12)).erase 0, ordinaryWeight p i) ≤
      11*p^(-(5/3 : ℝ)) := by
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin 12)).erase 0, p^(-(5/3 : ℝ)) :=
        Finset.sum_le_sum (fun i hi => ordinaryWeight_nonconstant p hp i (Finset.mem_erase.mp hi).1)
      _ = _ := by simp
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin 12)),ordinaryWeight_zero]
  linarith

theorem finite_euler_mass (σ C : ℝ) (hσ : 1 < σ) (hC : 0 ≤ C)
    (S : Finset Id) (hS : ∀ P ∈ S, Supported P) :
    (∏ P ∈ S, (1+C*(Ideal.absNorm P : ℝ)^(-σ))) ≤ Real.exp (C*rootMass σ) := by
  calc
    _ ≤ ∏ P ∈ S, Real.exp (C*(Ideal.absNorm P : ℝ)^(-σ)) := by
      apply Finset.prod_le_prod₀
      · intro P _
        positivity
      · intro P _
        simpa only [add_comm] using Real.add_one_le_exp (C*(Ideal.absNorm P : ℝ)^(-σ))
    _ = Real.exp (C*∑ P ∈ S, (Ideal.absNorm P : ℝ)^(-σ)) := by
      rw [Finset.mul_sum,Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (finite_root_mass σ hσ S hS) hC)

/-- A finite global bound independent of the prime pool and its cutoff.
Primality is needed for later unique factorization, not for this positive bound. -/
theorem ordinary_global_mass (S : Finset Id) (hS : ∀ P ∈ S, Supported P) :
    (∏ P ∈ S, ∑ i : Fin 12, ordinaryWeight (Ideal.absNorm P : ℝ) i) ≤
      Real.exp (11*rootMass (5/3)) := by
  calc
    _ ≤ ∏ P ∈ S, (1+11*(Ideal.absNorm P : ℝ)^(-(5/3 : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro P _
        exact Finset.sum_nonneg (fun i _ => ordinaryWeight_nonneg _ (Nat.cast_nonneg _) i)
      · intro P hP
        exact ordinary_local_mass _ (CenteredExceptionalCount.norm_one_le (hS P hP).1)
    _ ≤ _ := finite_euler_mass (5/3) 11 (by norm_num) (by norm_num) S hS

theorem ordinary_configuration_mass (S : Finset Id) (hS : ∀ P ∈ S, Supported P) :
    (∑ a ∈ Fintype.piFinset (fun _P : S => (Finset.univ : Finset (Fin 12))),
      ∏ P : S, ordinaryWeight (Ideal.absNorm P.val : ℝ) (a P)) ≤
      Real.exp (11*rootMass (5/3)) := by
  rw [← Finset.prod_univ_sum (fun _P : S => (Finset.univ : Finset (Fin 12)))
    (fun P : S => fun i : Fin 12 => ordinaryWeight (Ideal.absNorm P.val : ℝ) i)]
  have he : (∏ P : S, ∑ i : Fin 12, ordinaryWeight (Ideal.absNorm P.val : ℝ) i) =
      ∏ P ∈ S, ∑ i : Fin 12, ordinaryWeight (Ideal.absNorm P : ℝ) i := by
    exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
      (fun P : Id => ∑ i : Fin 12, ordinaryWeight (Ideal.absNorm P : ℝ) i)).symm
  rw [he]
  exact ordinary_global_mass S hS

theorem ordinary_configuration_identity (S : Finset Id) (x y : Id → ℂ) :
    (∏ P ∈ S, LocalKernels.ordinary (x P) (y P)) =
      ∑ a ∈ Fintype.piFinset (fun _P : S => (Finset.univ : Finset (Fin 12))),
        ∏ P : S, (ordinaryCoefficient (a P) : ℂ)*
          (x P.val)^(ordinaryExponent (a P)).1*(y P.val)^(ordinaryExponent (a P)).2 := by
  rw [← Finset.prod_univ_sum (fun _P : S => (Finset.univ : Finset (Fin 12)))
    (fun P : S => fun i : Fin 12 => (ordinaryCoefficient i : ℂ)*
      (x P.val)^(ordinaryExponent i).1*(y P.val)^(ordinaryExponent i).2)]
  simp_rw [← ordinary_exact]
  exact Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
    (fun P : Id => LocalKernels.ordinary (x P) (y P))

end
end Candidate.FourthPower.KernelForwardMass
