/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine colored active physical arm is exactly the H15 row polynomial.
Zero extension never imports the uncolored active carrier. -/
import Candidate.C092.transport.FixedFourierH15NativeFilled
import Candidate.C092.transport.FixedFourierH15NativeSelected

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion CanonicalRowCompletion
open CompletedGauss
open CenteredMomentSmooth CenteredMomentSecondCanonical CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentRowNorm CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled CenteredMomentHeckeColumnWindow
open CenteredMomentActiveSource CenteredMomentSecondActivePhysicalDictionary
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.Cycle092.SignedCenter QRH.Cycle092.FixedCubeGauss
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Coefficients that vanish in the genuine colored source contribute zero
before every divisor, ray, row and Fourier factor. -/
lemma active_window_arm_sum (η : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (G : Id) (hG : Supported G) (L : Id) (χ : RayCharacter) (A z : O)
    (θ X : ℝ) (V : ℝ→ℂ) :
    (∑I:sectorPool G hG.1 (activeSource S β),
      nativeGaussArm η t (activeSource S β) β G hG L χ A z I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) =
    (∑I:sectorPool G hG.1 S,nativeGaussArm η t S β G hG L χ A z I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) := by
  let f : Id→ℂ := fun I=>(if L ∣ I then
    ((β (G*I)*heightCoeff η t I)*idealRowHom A I)*rayCharacter χ (primaryGenerator I) else 0)*
      idealRowHom z I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ
  have he (T : Finset Id) :
      (∑I:sectorPool G hG.1 T,nativeGaussArm η t T β G hG L χ A z I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ)=
      ∑I∈sectorPool G hG.1 T,f I := by
    calc
      _ = ∑I:sectorPool G hG.1 T,f I := by
        apply Finset.sum_congr rfl
        intro I hi
        simp only [f,nativeGaussArm,divisorCoefficient,movingCoefficient,sectorElement_span]
        rfl
      _ = _ := Finset.sum_coe_sort (sectorPool G hG.1 T) f
  rw [he,he]
  apply sector_sum_active G hG.1 S β f
  intro I hI
  simp only [f,hI,zero_mul]
  split_ifs <;> simp

/-- This is the actual original colored active arm, with the original moving
frequency and Fourier window, equal to the exact polynomial paid by H15. -/
theorem active_window_eq_native {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id)
    (t θ X : ℝ) (V : ℝ→ℂ) :
    (∑I:sectorPool G hG.1 (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)),
      nativeGaussArm η t (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
        (TwistedRawSource.sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) G hG L χ D.A D.z I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) =
      nativeWindowPolynomial s ha D ω₁ ω₂ η χ G hG L t θ X V := by
  rw [RootColoredSeed.active,active_window_arm_sum]
  unfold nativeWindowPolynomial rowPolynomial nativeGaussArm
  apply Finset.sum_congr rfl
  intro I hi
  simp only [sectorElement_span]
  ring

/-- In particular, the authentic fixed arm is the packed row at A*z.
Only the frequency variable changes; no profile-radius equality is asserted. -/
theorem active_window_eq_packed {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id)
    (t θ X : ℝ) (V : ℝ→ℂ) :
    (∑I:sectorPool G hG.1 (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)),
      nativeGaussArm η t (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
        (TwistedRawSource.sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) G hG L χ D.A D.z I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) =
      fixedWindowRow s ha ω₁ ω₂ η χ G hG L t θ X V (D.A*D.z) := by
  rw [active_window_eq_native,nativeWindowPolynomial_absorb]
  rfl

#print axioms active_window_arm_sum
#print axioms active_window_eq_native
#print axioms active_window_eq_packed
end QRH.Cycle092.FixedFourierH15
