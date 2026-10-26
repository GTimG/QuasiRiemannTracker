/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal normalized frozen-squarefree centered rows on one common maximal pool.
Frozen ordinary ideals stay in the squarefree projector after cofactor extraction. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CorrectedCentered
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily QRH.Record1252270103Low QRH.Record1252270103Restoration
open QRH.Record1252270103KernelMass OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O

lemma zeroHom_monoid_apply (ψ:Ideal O→*₀ℂ)(I:Ideal O) : ψ.toMonoidHom I=ψ I := rfl

lemma centeredProfile_multiply (W₁ W₂:ℝ→ℂ)(X₁ X₂ Y₁ Y₂:ℝ)(d a:IdealPair):
    centeredProfile W₁ W₂ X₁ X₂ Y₁ Y₂ (multiplyPair d a)=
      centeredProfile W₁ W₂ (X₁/d.1.absNorm) (X₂/d.2.absNorm)
        (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) a := by
  simp only [centeredProfile,pairProfile_multiply]

/-- Exact normalization and fiber identity, with every frozen factor retained. -/
theorem normalized_newton_extracted_row (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)
    (A₁ A₂:Ideal O)(d:IdealPair)(hd:GoodPair d)(b X₁ X₂ Y₁ Y₂ T:ℝ)(hT:0<T):
    (Real.sqrt T:ℂ)⁻¹*newtonExtractedRow (commonPool b X₁ X₂ Y₁ Y₂)
      A₁ A₂ d ψ.toMonoidHom (frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂)=
      (ψ (d.1*d.2)/(Real.sqrt (pairNorm d):ℂ))*
        frozenCenteredRow ψ W₁ W₂ (A₁*d.1) (A₂*d.2) b
          (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) (T/pairNorm d) := by
  unfold newtonExtractedRow frozenCenteredRow commonPool
  rw [newton_residual_hole_pool d hd]
  simp only [max_div_div_right (show (0:ℝ)≤d.1.absNorm from Nat.cast_nonneg _),
    max_div_div_right (show (0:ℝ)≤d.2.absNorm from Nat.cast_nonneg _)]
  have he (a:IdealPair):frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ (d.1*a.1,d.2*a.2)=
      frozenProfile W₁ W₂ (A₁*d.1) (A₂*d.2) (X₁/d.1.absNorm) (X₂/d.2.absNorm)
        (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) a := by
    unfold frozenProfile
    rw [show (d.1*a.1,d.2*a.2)=multiplyPair d a from rfl,centeredProfile_multiply]
    simp only [multiplyPair,mul_assoc]
  simp_rw [he]
  simp only [mul_assoc,zeroHom_monoid_apply]
  rw [normalized_divisor_identity T (pairNorm d) hT (pairNorm_pos hd.1 hd.2.1)]
  ring

/-- The actual centered difference, not an arbitrary pair function, supplies
all support-only coprimality, depth and strict pole gates. -/
theorem normalized_centered_newton (P:Finset (Ideal O))(D M A₁ A₂:Ideal O)(depth:ℕ)
    (ψ:Ideal O→*₀ℂ)(W₁ W₂:ℝ→ℂ)(b X₁ X₂ Y₁ Y₂ T:ℝ)(hT:0<T)
    (hp:∀p∈P,Prime p)(hN:∀p∈P,16≤p.absNorm)(havoid:∀p∈P,¬p∣M)
    (hsupport:∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
      frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→
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
  have hh:=newton_corrected_finite_rows P D M depth (commonPool b X₁ X₂ Y₁ Y₂) A₁ A₂
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

end
end QRH.Record1252270103Source.High.CorrectedCentered
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.normalized_newton_extracted_row
#print axioms QRH.Record1252270103Source.High.CorrectedCentered.normalized_centered_newton
