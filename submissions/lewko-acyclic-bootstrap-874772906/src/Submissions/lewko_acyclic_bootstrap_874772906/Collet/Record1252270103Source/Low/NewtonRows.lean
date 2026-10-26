/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.NewtonRowsCore

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Record1252270103Source
open QRH.Record1252270103KernelMass
local notation "O" => ActualEisensteinCubic.O

def newtonDivisorPair (S A : Finset (Ideal O)) : IdealPair := (∏p∈A,p,∏p∈S\A,p)

def newtonExtractedRow (E : Finset IdealPair) (A₁ A₂ : Ideal O)
    (d : IdealPair) (ψ : Ideal O →* ℂ) (f : IdealPair→ℂ) : ℂ :=
  ψ (d.1*d.2)*∑a∈newtonResidualPairs E d,
    (squarefreeIndicator ((A₁*d.1*a.1)*(A₂*d.2*a.2)):ℂ)*
      ψ (a.1*a.2)*f (d.1*a.1,d.2*a.2)

theorem squarefree_residual_pair (A₁ A₂ I J : Ideal O)
    (hs : Squarefree ((A₁*I)*(A₂*J))) : Squarefree (I*J) := by
  have he : (A₁*I)*(A₂*J)=(A₁*A₂)*(I*J) := by ring
  rw [he] at hs
  exact hs.of_mul_right

/-- Pointwise expansion retains the literal squarefree mask, including its
zero branch. No squarefree hypothesis is imposed on the whole finite box. -/
theorem newton_polynomial_squarefree (P : Finset (Ideal O)) (r0 depth : ℕ)
    (A₁ A₂ I J : Ideal O) (hp : ∀p∈P,Prime p) :
    (idealNewtonPolynomial P r0 depth (I*J):ℂ)*
      (squarefreeIndicator ((A₁*I)*(A₂*J)):ℂ)=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        (newtonCoefficient P.card r0 S.card:ℂ)*
          ((idealDvdIndicator (newtonDivisorPair S A).1 I*
            idealDvdIndicator (newtonDivisorPair S A).2 J:ℝ):ℂ)*
          (squarefreeIndicator ((A₁*I)*(A₂*J)):ℂ) := by
  by_cases hs : Squarefree ((A₁*I)*(A₂*J))
  · rw [idealNewtonPolynomial_assignments P r0 depth I J hp
      (squarefree_residual_pair A₁ A₂ I J hs)]
    push_cast
    simp only [Finset.sum_mul,newtonDivisorPair]
  · simp [squarefreeIndicator,hs]

/-- Exact finite shifted-Newton expansion at the actual row level. The pair
function may be the centered profile difference or any later completed row.
Its argument and the original squarefree mask are reconstructed literally. -/
theorem newton_polynomial_finite_rows (P : Finset (Ideal O)) (r0 depth : ℕ)
    (E : Finset IdealPair) (A₁ A₂ : Ideal O) (ψ : Ideal O →* ℂ)
    (f : IdealPair→ℂ) (hp : ∀p∈P,Prime p) :
    (∑n∈E,(idealNewtonPolynomial P r0 depth (n.1*n.2):ℂ)*
      (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*f n)=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        (newtonCoefficient P.card r0 S.card:ℂ)*
          newtonExtractedRow E A₁ A₂ (newtonDivisorPair S A) ψ f := by
  let T := P.powerset.filter (fun S=>S.card≤depth)
  calc
    _ = ∑n∈E,∑S∈T,∑A∈S.powerset,
        (newtonCoefficient P.card r0 S.card:ℂ)*
          (((idealDvdIndicator (newtonDivisorPair S A).1 n.1*
            idealDvdIndicator (newtonDivisorPair S A).2 n.2:ℝ):ℂ)*
            (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*f n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [newton_polynomial_squarefree P r0 depth A₁ A₂ n.1 n.2 hp]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ = ∑S∈T,∑A∈S.powerset,(newtonCoefficient P.card r0 S.card:ℂ)*
        ∑n∈E,((idealDvdIndicator (newtonDivisorPair S A).1 n.1*
          idealDvdIndicator (newtonDivisorPair S A).2 n.2:ℝ):ℂ)*
          (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*f n := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro A _
      rw [newton_finite_squarefree_extract E (newtonDivisorPair S A) A₁ A₂ ψ f]
      rfl

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.newton_polynomial_squarefree
#print axioms QRH.Record1252270103Low.newton_polynomial_finite_rows
