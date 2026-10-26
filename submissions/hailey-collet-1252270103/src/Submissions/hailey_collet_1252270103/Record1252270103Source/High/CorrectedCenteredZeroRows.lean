/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Zero-aware normalized centered Newton expansion. Coprimality, count and pole
conditions are required only on actual nonzero character/profile summands.
The preceding seven-module package is preserved unchanged. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CorrectedCenteredMarked
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CorrectedCentered
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103KernelMass OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O

theorem newton_corrected_finite_rows_nonzero (P : Finset (Ideal O)) (D M : Ideal O)
    (depth : ℕ) (E : Finset IdealPair) (A₁ A₂ : Ideal O)
    (ψ : Ideal O →* ℂ) (f : IdealPair→ℂ) (hp : ∀p∈P,Prime p)
    (havoid : ∀p∈P,¬p∣M)
    (hsupport : ∀n∈E,Squarefree ((A₁*n.1)*(A₂*n.2)) → f n≠0 → ψ (n.1*n.2)≠0 →
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
    · by_cases hψ : ψ (n.1*n.2)=0
      · simp only [hψ,mul_zero,zero_mul]
      · obtain ⟨hc,hd,hpole⟩ := hsupport n hn hs hf hψ
        have hdepth : (idealDividingPool P (M*n.1*n.2)).card≤depth := by
          rwa [ideal_dividing_pool_drop_marked P M n.1 n.2 hp havoid]
        have hreal := ideal_correction_shifted_polynomial P D (M*n.1*n.2) depth hp hc hdepth hpole
        rw [idealNewtonPolynomial_drop_marked P _ depth M n.1 n.2 hp havoid] at hreal
        have hcast := congrArg (fun x : ℝ=>(x:ℂ)) hreal
        push_cast at hcast ⊢
        rw [hcast]
  · simp only [squarefreeIndicator,if_neg hs,Int.cast_zero,mul_zero,zero_mul]

theorem normalized_centered_newton_nonzero (P:Finset (Ideal O))(D M A₁ A₂:Ideal O)(depth:ℕ)
    (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)(b X₁ X₂ Y₁ Y₂ T:ℝ)(hT:0<T)
    (hp:∀p∈P,Prime p)(hN:∀p∈P,16≤p.absNorm)(havoid:∀p∈P,¬p∣M)
    (hsupport:∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
      frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→ ψ (n.1*n.2)≠0→
      IsCoprime D (M*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*(M*n.1*n.2))).card<P.card) :
    correctedCenteredRow P D M A₁ A₂ ψ W₁ W₂ b X₁ X₂ Y₁ Y₂ T=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        ((newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
          ψ ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)/
            (Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ))*
          frozenCenteredRow ψ W₁ W₂ (A₁*(newtonDivisorPair S A).1) (A₂*(newtonDivisorPair S A).2) b
            (X₁/(newtonDivisorPair S A).1.absNorm) (X₂/(newtonDivisorPair S A).2.absNorm)
            (Y₁/(newtonDivisorPair S A).1.absNorm) (Y₂/(newtonDivisorPair S A).2.absNorm)
            (T/pairNorm (newtonDivisorPair S A)) := by
  unfold correctedCenteredRow
  have hh:=newton_corrected_finite_rows_nonzero P D M depth (commonPool b X₁ X₂ Y₁ Y₂) A₁ A₂
    ψ.toMonoidHom (frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂) hp havoid hsupport
  simp only [zeroHom_monoid_apply] at hh
  rw [hh,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hd:=newton_divisor_pair_good P S A
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) (Finset.mem_powerset.mp hA) hp hN
  have he:=normalized_newton_extracted_row ψ W₁ W₂ A₁ A₂ (newtonDivisorPair S A) hd
    b X₁ X₂ Y₁ Y₂ T hT
  calc
    _ = (newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
      ((Real.sqrt T:ℂ)⁻¹*newtonExtractedRow (commonPool b X₁ X₂ Y₁ Y₂) A₁ A₂
        (newtonDivisorPair S A) ψ.toMonoidHom (frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂)) := by ring
    _ = _ := by rw [he];ring

theorem normalized_centered_newton_marked_nonzero {κ:Type*} (P:Finset (Ideal O))
    (slots:Finset κ)(marked:κ→Ideal O)(D A₁ A₂:Ideal O)(depth:ℕ)
    (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)(b X₁ X₂ Y₁ Y₂ T:ℝ)(hT:0<T)
    (hp:∀p∈P,Prime p)(hN:∀p∈P,16≤p.absNorm)(havoid:∀p∈P,∀i∈slots,¬p∣marked i)
    (hsupport:∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
      frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→ ψ (n.1*n.2)≠0→
      IsCoprime D ((∏i∈slots,marked i)*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*((∏i∈slots,marked i)*n.1*n.2))).card<P.card) :
    correctedCenteredRow P D (∏i∈slots,marked i) A₁ A₂ ψ W₁ W₂ b X₁ X₂ Y₁ Y₂ T=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        ((newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
          ψ ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)/
            (Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ))*
          frozenCenteredRow ψ W₁ W₂ (A₁*(newtonDivisorPair S A).1) (A₂*(newtonDivisorPair S A).2) b
            (X₁/(newtonDivisorPair S A).1.absNorm) (X₂/(newtonDivisorPair S A).2.absNorm)
            (Y₁/(newtonDivisorPair S A).1.absNorm) (Y₂/(newtonDivisorPair S A).2.absNorm)
            (T/pairNorm (newtonDivisorPair S A)) := by
  exact normalized_centered_newton_nonzero P D (∏i∈slots,marked i) A₁ A₂ depth ψ W₁ W₂
    b X₁ X₂ Y₁ Y₂ T hT hp hN (pool_avoids_marked_product P slots marked hp havoid) hsupport

end
end QRH.Record1252270103Source.High.CorrectedCentered
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.newton_corrected_finite_rows_nonzero
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.normalized_centered_newton_nonzero
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.normalized_centered_newton_marked_nonzero
