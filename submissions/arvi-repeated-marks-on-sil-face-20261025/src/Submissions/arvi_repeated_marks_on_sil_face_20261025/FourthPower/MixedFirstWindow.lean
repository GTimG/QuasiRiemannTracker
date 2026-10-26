/- Copyright (c) 2026 Sil. Apache-2.0.
exact structured first-Gauss row and common column-window integral.
The source coefficient is the actual tuple-weighted originalColumn.
The character presentation is supplied by FixedPair.left_height or
FixedPair.right_height; no arbitrary-multiplier moment is assumed.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedOriginalCoprimality
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ConjugateWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss RayFourExpansion ConcretePrimeRowBridge FourierBridge
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildAssembly
open CenteredMomentSecondHeightFamily CenteredMomentGaussEnergy CenteredMomentSmooth
open CenteredMomentConjugateWindow
open MixedHeightEnergy MixedOriginalCoprimality MixedLiteralAllocation
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

variable (S H : Finset PrimeIdeal) (pool : α→Finset Id)
  (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
  (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
  (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
  (C G : Id) (hG : G≠0)

local notation "βoriginal" =>
  originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂
local notation "Qsource" => finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
local notation "Afirst" => CenteredMomentFirstPhysicalSource.columns C G hG Qsource
local notation "afirst" => CenteredMomentFirstPhysicalSource.element C G hG Qsource
local notation "hafirst" => CenteredMomentFirstPhysicalSource.element_supported C G hG Qsource

/-- The left first-child coefficient after exact ray/divisor separation.
Use F=leftCoefficient and hτ=FixedPair.left_height, or the corresponding
right presentation. The entire source restriction stays in βoriginal. -/
theorem first_gauss_window (η τ : Character) (F : O→ℂ) (ξ : RayCharacter)
    (hτ : ∀I : Id,Supported I→∀t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (L : Id) (t θ Xwindow : ℝ) (hXwindow : 0<Xwindow)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    gaussPolynomial Finset.univ afirst hafirst
      (fun i : Afirst=>divisorCoefficient L afirst
        (fun j : Afirst=>βoriginal (G*j)*
          rowWeight η (fixedBadMask*idealGenerator R) 1 1 t j*F (afirst j)) ξ i*
        columnPhase V (Real.log ((i.val.absNorm:ℝ)/Xwindow)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log Xwindow)*
        gaussPolynomial Finset.univ afirst hafirst
          (fun i : Afirst=>(if L∣i.val then βoriginal (G*i) else 0)*
            heightCoeff τ (t+2*Real.pi*(w-θ)) i) z := by
  have hcoeff (i : Afirst) :
      divisorCoefficient L afirst
        (fun j : Afirst=>βoriginal (G*j)*
          rowWeight η (fixedBadMask*idealGenerator R) 1 1 t j*F (afirst j)) ξ i=
        (if L∣i.val then βoriginal (G*i) else 0)*heightCoeff τ t i := by
    have hi := CenteredMomentFirstPhysicalSource.column_supported C G hG Qsource i
    have hh := original_divisor_column S H pool d hd R seed ν Wslot P W₁ W₂
      b X₁ X₂ Y₁ Y₂ η τ F ξ hτ G L i hi t
    simpa only [divisorCoefficient,CenteredMomentFirstPhysicalSource.element,
      CenteredMomentSourceRow.primary_span_supported i.val hi] using hh
  calc
    _ = gaussPolynomial Finset.univ afirst hafirst
        (fun i : Afirst=>(if L∣i.val then βoriginal (G*i) else 0)*heightCoeff τ t i*
          columnPhase V (Real.log ((i.val.absNorm:ℝ)/Xwindow)) θ) z := by
      apply congrArg (fun c : Afirst→ℂ=>gaussPolynomial Finset.univ afirst hafirst c z)
      funext i
      rw [hcoeff i]
    _ = _ := by
      simpa only [CenteredMomentFirstPhysicalSource.element_span] using
        gauss_column_integral Finset.univ afirst hafirst
          (fun i : Afirst=>if L∣i.val then βoriginal (G*i) else 0)
          τ t θ Xwindow hXwindow V hVc hVs z

/-- The right child has the conjugated column window. Its exact common
Fourier integral uses the conjugated profile and reversed window phase.
All coefficients, source domains and residual divisibility are unchanged. -/
theorem first_gauss_conjugate_window (η τ : Character) (F : O→ℂ) (ξ : RayCharacter)
    (hτ : ∀I : Id,Supported I→∀t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (L : Id) (t θ Xwindow : ℝ) (hXwindow : 0<Xwindow)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    gaussPolynomial Finset.univ afirst hafirst
      (fun i : Afirst=>divisorCoefficient L afirst
        (fun j : Afirst=>βoriginal (G*j)*
          rowWeight η (fixedBadMask*idealGenerator R) 1 1 t j*F (afirst j)) ξ i*
        star (columnPhase V (Real.log ((i.val.absNorm:ℝ)/Xwindow)) θ)) z=
      ∫ w : ℝ,columnDensity (fun x=>star (V x)) (conjugate_compact V hVc)
          (conjugate_smooth V hVs) w*logPhase (-θ-w) (Real.log Xwindow)*
        gaussPolynomial Finset.univ afirst hafirst
          (fun i : Afirst=>(if L∣i.val then βoriginal (G*i) else 0)*
            heightCoeff τ (t+2*Real.pi*(w+θ)) i) z := by
  simp_rw [star_columnPhase]
  simpa only [sub_neg_eq_add] using first_gauss_window S H pool d hd R seed ν Wslot P W₁ W₂
    b X₁ X₂ Y₁ Y₂ C G hG η τ F ξ hτ L t (-θ) Xwindow hXwindow
    (fun x=>star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) z

end
end Candidate.FourthPower.MixedFirstWindow
