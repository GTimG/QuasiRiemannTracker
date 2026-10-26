/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.NewtonRows

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Record1252270103Source
open QRH.Record1252270103KernelMass
local notation "O" => ActualEisensteinCubic.O

/-- Exact rational correction on the actual supported finite row. Count,
coprimality and pole premises are required only where the literal squarefree
mask and the original pair function both survive. -/
theorem newton_corrected_finite_rows (P : Finset (Ideal O)) (D M : Ideal O)
    (depth : ℕ) (E : Finset IdealPair) (A₁ A₂ : Ideal O)
    (ψ : Ideal O →* ℂ) (f : IdealPair→ℂ) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,¬p∣M)
    (hsupport : ∀n∈E,Squarefree ((A₁*n.1)*(A₂*n.2)) → f n≠0 →
      IsCoprime D (M*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*(M*n.1*n.2))).card<P.card) :
    (∑n∈E,(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P (D*(M*n.1*n.2))).card)):ℂ)*
      (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*f n)=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        (newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
          newtonExtractedRow E A₁ A₂ (newtonDivisorPair S A) ψ f := by
  rw [←newton_polynomial_finite_rows P (idealDividingPool P D).card depth E A₁ A₂ ψ f hp]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : Squarefree ((A₁*n.1)*(A₂*n.2))
  · by_cases hf : f n=0
    · simp only [hf,mul_zero]
    · obtain ⟨hc,hd,hpole⟩ := hsupport n hn hs hf
      have hdepth : (idealDividingPool P (M*n.1*n.2)).card≤depth := by
        rwa [ideal_dividing_pool_drop_marked P M n.1 n.2 hp havoid]
      have hreal := ideal_correction_shifted_polynomial P D (M*n.1*n.2) depth hp hc hdepth hpole
      rw [idealNewtonPolynomial_drop_marked P _ depth M n.1 n.2 hp havoid] at hreal
      have hcast := congrArg (fun x : ℝ=>(x:ℂ)) hreal
      push_cast at hcast ⊢
      rw [hcast]
  · simp only [squarefreeIndicator,if_neg hs,Int.cast_zero,mul_zero,zero_mul]

/-- The actual marked slots appear explicitly. No exclusion is inferred from
the squarefree ordinary pair, and the whole finite Newton depth is fixed before
the row, character and pair function are chosen. -/
theorem newton_corrected_marked_rows {ι : Type*} (P : Finset (Ideal O))
    (slots : Finset ι) (marked : ι→Ideal O) (D : Ideal O) (depth : ℕ)
    (E : Finset IdealPair) (A₁ A₂ : Ideal O) (ψ : Ideal O →* ℂ)
    (f : IdealPair→ℂ) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,∀i∈slots,¬p∣marked i)
    (hsupport : ∀n∈E,Squarefree ((A₁*n.1)*(A₂*n.2)) → f n≠0 →
      IsCoprime D ((∏i∈slots,marked i)*n.1*n.2) ∧
        (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*((∏i∈slots,marked i)*n.1*n.2))).card<P.card) :
    (∑n∈E,(((P.card:ℝ)/((P.card:ℝ)-
        (idealDividingPool P (D*((∏i∈slots,marked i)*n.1*n.2))).card)):ℂ)*
      (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*f n)=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        (newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
          newtonExtractedRow E A₁ A₂ (newtonDivisorPair S A) ψ f :=
  newton_corrected_finite_rows P D (∏i∈slots,marked i) depth E A₁ A₂ ψ f hp
    (pool_avoids_marked_product P slots marked hp havoid) hsupport

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.newton_corrected_finite_rows
#print axioms QRH.Record1252270103Low.newton_corrected_marked_rows
