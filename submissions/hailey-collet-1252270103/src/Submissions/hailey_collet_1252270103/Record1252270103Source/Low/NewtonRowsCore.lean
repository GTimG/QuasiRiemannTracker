/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.NewtonIdealCorrection
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.FiniteReindex

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Record1252270103Source
open QRH.Record1252270103KernelMass
local notation "O" => ActualEisensteinCubic.O

/-- The exact finite cofactor image for one selected divisor pair. -/
def newtonResidualPairs (E : Finset IdealPair) (d : IdealPair) : Finset IdealPair :=
  (E.filter (fun n=>d.1∣n.1 ∧ d.2∣n.2)).image (fun n=>cofactorPair n.1 n.2 d)

theorem newton_cofactor_reconstruct (d n : IdealPair) (hd : d.1∣n.1 ∧ d.2∣n.2) :
    multiplyPair d (cofactorPair n.1 n.2 d)=n := by
  apply Prod.ext
  · exact idealCofactor_mul hd.1
  · exact idealCofactor_mul hd.2

theorem newton_cofactor_injective (E : Finset IdealPair) (d : IdealPair) :
    Set.InjOn (fun n : IdealPair=>cofactorPair n.1 n.2 d)
      (↑(E.filter (fun n=>d.1∣n.1 ∧ d.2∣n.2)) : Set IdealPair) := by
  intro n hn m hm heq
  have hn' := newton_cofactor_reconstruct d n (Finset.mem_filter.mp hn).2
  have hm' := newton_cofactor_reconstruct d m (Finset.mem_filter.mp hm).2
  exact hn'.symm.trans ((congrArg (multiplyPair d) heq).trans hm')

/-- Exact finite divisor extraction with the original multiplicative character.
The arbitrary pair function is evaluated at the reconstructed original pair. -/
theorem newton_finite_character_extract (E : Finset IdealPair) (d : IdealPair)
    (ψ : Ideal O →* ℂ) (f : IdealPair→ℂ) :
    (∑n∈E,((idealDvdIndicator d.1 n.1*idealDvdIndicator d.2 n.2 : ℝ):ℂ)*
      ψ (n.1*n.2)*f n)=
      ψ (d.1*d.2)*∑a∈newtonResidualPairs E d,ψ (a.1*a.2)*f (multiplyPair d a) := by
  have hf : (∑n∈E,((idealDvdIndicator d.1 n.1*idealDvdIndicator d.2 n.2 : ℝ):ℂ)*
      ψ (n.1*n.2)*f n)=
      ∑n∈E.filter (fun n=>d.1∣n.1 ∧ d.2∣n.2),ψ (n.1*n.2)*f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hi : d.1∣n.1 <;> by_cases hj : d.2∣n.2 <;>
      simp [idealDvdIndicator,hi,hj]
  rw [hf,newtonResidualPairs,Finset.sum_image (newton_cofactor_injective E d),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hrec := newton_cofactor_reconstruct d n (Finset.mem_filter.mp hn).2
  have hψ := character_pair_multiply ψ d (cofactorPair n.1 n.2 d)
  rw [hrec] at hψ
  rw [hrec,hψ]
  ring

/-- Literal squarefree mask with fixed extracted ordinary ideals A1,A2. -/
theorem newton_finite_squarefree_extract (E : Finset IdealPair) (d : IdealPair)
    (A₁ A₂ : Ideal O) (ψ : Ideal O →* ℂ) (f : IdealPair→ℂ) :
    (∑n∈E,((idealDvdIndicator d.1 n.1*idealDvdIndicator d.2 n.2 : ℝ):ℂ)*
      (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*f n)=
      ψ (d.1*d.2)*∑a∈newtonResidualPairs E d,
        (squarefreeIndicator ((A₁*d.1*a.1)*(A₂*d.2*a.2)):ℂ)*
          ψ (a.1*a.2)*f (d.1*a.1,d.2*a.2) := by
  have h := newton_finite_character_extract E d ψ
    (fun n=>(squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*f n)
  calc
    _ = ∑n∈E,((idealDvdIndicator d.1 n.1*idealDvdIndicator d.2 n.2 : ℝ):ℂ)*
        ψ (n.1*n.2)*((squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*f n) := by
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := h
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      simp only [multiplyPair,mul_assoc]
      ring

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.newton_finite_character_extract
#print axioms QRH.Record1252270103Low.newton_finite_squarefree_extract
