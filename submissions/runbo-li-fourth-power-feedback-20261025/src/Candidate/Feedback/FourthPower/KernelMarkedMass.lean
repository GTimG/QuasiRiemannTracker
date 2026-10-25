/- Copyright (c) 2026 Sil. Apache-2.0.
The marked forward correction B-H. Only a fixed number of labelled slots
supplies a correction: no unrestricted marked Euler product is introduced.
-/
import Candidate.Feedback.FourthPower.KernelForwardMass

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.KernelMarkedMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open SieveDescent SieveCentralReference
local notation "Id" => Ideal ActualEisensteinCubic.O

def markedExponent : Fin 14 → ℕ × ℕ :=
  ![(1,0),(0,1),(1,1),(0,5),(1,4),(2,3),(3,2),(4,1),(5,0),(1,5),(2,4),(3,3),(4,2),(5,1)]

def markedCoefficient : Fin 14 → ℤ := ![-1,-1,1,1,1,1,1,1,1,-1,-1,-1,-1,-1]

theorem critical_marked_weight (p : ℝ) (hp : 0 < p) (j k : ℕ) :
    p^(-(((j : ℝ)+k+1)/2))*p^(((k : ℝ)-j-1)/6) =
      p^(-((2*(j : ℝ)+k+2)/3)) := by
  rw [← Real.rpow_add hp]
  congr 1
  ring

theorem marked_exact (x y : ℂ) :
    LocalKernels.base x y-LocalKernels.ordinary x y = ∑ i : Fin 14,
      (markedCoefficient i : ℂ)*x^(markedExponent i).1*y^(markedExponent i).2 := by
  rw [LocalKernels.ordinary_expansion]
  norm_num [LocalKernels.base,markedExponent,markedCoefficient,Fin.sum_univ_succ]
  ring

def markedWeight (p : ℝ) (i : Fin 14) : ℝ :=
  |(markedCoefficient i : ℝ)| * p^(-((2*(markedExponent i).1+(markedExponent i).2+2 : ℝ)/3))

theorem markedWeight_nonneg (p : ℝ) (hp : 0 ≤ p) (i : Fin 14) : 0 ≤ markedWeight p i := by
  unfold markedWeight
  positivity

theorem marked_term_bound (p : ℝ) (hp : 0 < p) (x y z : ℂ)
    (hx : ‖x‖ ≤ p^(-(2/3 : ℝ))) (hy : ‖y‖ ≤ p^(-(1/3 : ℝ)))
    (hz : ‖z‖ ≤ p^(-(2/3 : ℝ))) (i : Fin 14) :
    ‖(markedCoefficient i : ℂ)*z*x^(markedExponent i).1*y^(markedExponent i).2‖ ≤
      markedWeight p i := by
  have he : p^(-(2/3 : ℝ))*(p^(-(2/3 : ℝ)))^(markedExponent i).1 *
      (p^(-(1/3 : ℝ)))^(markedExponent i).2 =
      p^(-((2*(markedExponent i).1+(markedExponent i).2+2 : ℝ)/3)) := by
    simp only [← Real.rpow_natCast,← Real.rpow_mul hp.le,← Real.rpow_add hp]
    congr 1
    ring
  simp only [norm_mul,norm_pow,Complex.norm_intCast]
  calc
    _ ≤ (|(markedCoefficient i : ℝ)| * p^(-(2/3 : ℝ)))*
        (p^(-(2/3 : ℝ)))^(markedExponent i).1*(p^(-(1/3 : ℝ)))^(markedExponent i).2 := by
      gcongr
    _ = markedWeight p i := by
      rw [mul_assoc,mul_assoc,← mul_assoc (p^(-(2/3 : ℝ))),he]
      rfl

theorem markedWeight_le (p : ℝ) (hp : 1 ≤ p) (i : Fin 14) : markedWeight p i ≤ p⁻¹ := by
  have hc : |(markedCoefficient i : ℝ)| = 1 := by fin_cases i <;> norm_num [markedCoefficient]
  have he : (3 : ℝ) ≤ 2*(markedExponent i).1+(markedExponent i).2+2 := by
    fin_cases i <;> norm_num [markedExponent]
  rw [markedWeight,hc,one_mul,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hp (by linarith)

theorem marked_local_mass (p : ℝ) (hp : 1 ≤ p) :
    (∑ i : Fin 14, markedWeight p i) ≤ 14*p⁻¹ := by
  calc
    _ ≤ ∑ _i : Fin 14, p⁻¹ := Finset.sum_le_sum (fun i _ => markedWeight_le p hp i)
    _ = _ := by simp

theorem marked_pool_mass (δ : ℝ) (hδ : 0 < δ) (X : ℝ) (hX : 0 < X)
    (S : Finset Id) (hS : ∀ P ∈ S, Supported P ∧ (Ideal.absNorm P : ℝ) ≤ X) :
    (∑ q : S × Fin 14, markedWeight (Ideal.absNorm q.1.val : ℝ) q.2) ≤
      14*X^δ*rootMass (1+δ) := by
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ P : S, 14*(Ideal.absNorm P.val : ℝ)⁻¹ := Finset.sum_le_sum (fun P _ =>
      marked_local_mass _ (CenteredExceptionalCount.norm_one_le (hS P.val P.property).1.1))
    _ = 14*∑ P ∈ S, (Ideal.absNorm P : ℝ)⁻¹ := by
      rw [← Finset.mul_sum,Finset.sum_coe_sort S (fun P : Id => (Ideal.absNorm P : ℝ)⁻¹)]
    _ ≤ 14*(X^δ*rootMass (1+δ)) :=
      mul_le_mul_of_nonneg_left (reciprocal_mass δ hδ X hX S hS) (by norm_num)
    _ = _ := by ring

/-- Absolute mass for a fixed labelled slot family. The upper family allows
collisions, so imposing distinctness or forbidden-prime restrictions only reduces it. -/
theorem marked_assignments_subpower {α : Type*} [Fintype α] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset Id,
      (∀ P ∈ S, Supported P ∧ (Ideal.absNorm P : ℝ) ≤ X) →
      (∑ a : α → S × Fin 14, ∏ i : α,
        markedWeight (Ideal.absNorm (a i).1.val : ℝ) (a i).2) ≤ C*X^ε := by
  let δ := ε/((Fintype.card α : ℝ)+1)
  have hd : 0 < (Fintype.card α : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hd
  let B := 14*rootMass (1+δ)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (rootMass_nonneg _)
  refine ⟨(B+1)^(Fintype.card α),by positivity,?_⟩
  intro X hX S hS
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hpool : (∑ q : S × Fin 14, markedWeight (Ideal.absNorm q.1.val : ℝ) q.2) ≤ B*X^δ := by
    convert marked_pool_mass δ hδ X hX0 S hS using 1
    dsimp only [B]
    ring
  have hexp : δ*(Fintype.card α : ℝ) ≤ ε := by
    have he : δ*((Fintype.card α : ℝ)+1) = ε := div_mul_cancel₀ ε (ne_of_gt hd)
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ.le).trans_eq he
  calc
    _ = ∏ _i : α, ∑ q : S × Fin 14, markedWeight (Ideal.absNorm q.1.val : ℝ) q.2 :=
      (Fintype.prod_sum (fun _i : α => fun q : S × Fin 14 => markedWeight (Ideal.absNorm q.1.val : ℝ) q.2)).symm
    _ ≤ ∏ _i : α, B*X^δ := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun q _ => markedWeight_nonneg _ (Nat.cast_nonneg _) q.2)
      · intro i _
        exact hpool
    _ = B^(Fintype.card α)*X^(δ*(Fintype.card α : ℝ)) := by
      rw [Finset.prod_const,Finset.card_univ,mul_pow,
        ← Real.rpow_natCast (X^δ) (Fintype.card α),← Real.rpow_mul hX0.le]
    _ ≤ (B+1)^(Fintype.card α)*X^ε :=
      mul_le_mul (pow_le_pow_left₀ hB (le_add_of_nonneg_right zero_le_one) _)
        (Real.rpow_le_rpow_of_exponent_le hX hexp) (by positivity) (by positivity)

end
end Candidate.Feedback.FourthPower.KernelMarkedMass
