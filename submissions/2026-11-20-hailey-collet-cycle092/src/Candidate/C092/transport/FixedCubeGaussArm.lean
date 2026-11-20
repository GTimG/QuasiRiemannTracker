/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussExpansion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion RayFourExpansion CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Authentic character identification for the original native Gauss arm.
The mask condition is essential: native Poisson permits arbitrary m, whereas
completion by m^6 inserts its actual coprimality mask. -/
theorem nativeGaussArm_eq_fixedCoefficient (D : FixedCubeDatum) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C : Id) (hC : Supported C) (L : Id) (I : sectorPool C hC.1 S)
    (hcop : IsCoprime (I:Id) (Ideal.span {D.m})) :
    nativeGaussArm η t S β C hC L χ D.A D.z I=
      if L∣(I:Id) then β (C*I)*(Ideal.absNorm (I:Id):ℂ)^(Complex.I*t)*D.actualCoefficient I else 0 := by
  have hI := sectorPool_supported C hC.1 S I
  have hcoeff (θ : Character) : idealCoeff θ (I:Id)=elementCoeff θ (sectorElement C hC.1 S I) := by
    simpa only [primary_span_supported (I:Id) hI,sectorElement] using
      idealCoeff_span θ (supported_primaryGenerator_ne_zero (I:Id) hI)
  have hc := childCharacter_primary η χ (sectorElement C hC.1 S I)
    (sectorElement_supported C hC.1 S I) (sectorElement_primary C hC.1 S I)
  rw [←hcoeff (childCharacter η χ),←hcoeff η] at hc
  have hs := idealRowHom_sixth_mask D.m (I:Id) hI
  rw [ite_eq_left hcop] at hs
  have hact : D.actualCoefficient (I:Id)=
      (idealCoeff η (I:Id)*rayCharacter χ (sectorElement C hC.1 S I))*
        (idealRowHom D.A (I:Id)*idealRowHom D.z (I:Id)) := by
    unfold FixedCubeDatum.actualCoefficient
    rw [idealRowHom_argument_mul,hs,one_mul,hη,hc,idealRowHom_argument_mul]
  simp only [nativeGaussArm,divisorCoefficient,movingCoefficient,sectorElement_span,heightCoeff,hact]
  split_ifs <;> ring

#print axioms nativeGaussArm_eq_fixedCoefficient
set_option pp.proofs false in
#print QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly.originalColumn_coprime
open Lean Elab Command in
run_cmd do
  let e ← getEnv
  for (n,_) in e.constants.toList do
    if n.toString.endsWith "originalColumn_coprime" then logInfo m!"{n}"
end
end QRH.Cycle092.FixedCubeGauss
