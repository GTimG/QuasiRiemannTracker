/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussArm

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedHeightEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def nativeSourceMask (r : Source ι a b) : O := fixedBadMask*idealGenerator r.R

/-- The actual coefficient supplies its original artificial ideal puncture. -/
theorem sourceCoefficient_coprime (r : Source ι a b) (ha : 0<a) (seed J : Id)
    (hβ : sourceCoefficient r ha seed J≠0) : IsCoprime J r.R := by
  exact QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly.originalColumn_coprime
    r.S r.H r.pool r.d r.hd r.R seed r.ν r.Wslot r.P _ _ b r.X₁ r.X₂ r.Y₁ r.Y₂ J hβ

/-- Supportedness pays the fixed bad primes; the existing source puncture
pays R. No arbitrary artificial m can be inserted at this step. -/
theorem supported_coprime_nativeSourceMask (r : Source ι a b) (I : Id)
    (hI : Supported I) (hIR : IsCoprime I r.R) :
    IsCoprime I (Ideal.span {nativeSourceMask r}) := by
  have hc : IsCoprime I (Ideal.span {fixedBadMask}) := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact (fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)).symm
  rw [nativeSourceMask,←Ideal.span_singleton_mul_span_singleton,span_idealGenerator]
  exact hc.mul_right hIR

/-- Discharges the completion mask from the genuine sector coefficient. -/
theorem source_sector_coprime_nativeSourceMask (r : Source ι a b) (ha : 0<a)
    (C : Id) (hC : Supported C) (I : sectorPool C hC.1 (Second.Concrete.S0 r ha))
    (hβ : sourceCoefficient r ha 1 (C*I)≠0) :
    IsCoprime (I:Id) (Ideal.span {nativeSourceMask r}) := by
  exact supported_coprime_nativeSourceMask r I
    (sectorPool_supported C hC.1 _ I)
    ((sourceCoefficient_coprime r ha 1 (C*I) hβ).of_isCoprime_of_dvd_left (dvd_mul_left _ _))

/-- Exact authentic-row identification for the original second Gauss arm
with the actual artificial source mask, including the zero coefficient case. -/
theorem source_nativeGaussArm_eq_fixedCoefficient (r : Source ι a b) (ha : 0<a)
    (D : FixedCubeDatum) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (t : ℝ) (C : Id) (hC : Supported C) (L : Id)
    (I : sectorPool C hC.1 (Second.Concrete.S0 r ha)) :
    nativeGaussArm η t (Second.Concrete.S0 r ha) (sourceCoefficient r ha 1) C hC L χ D.A D.z I=
      if L∣(I:Id) then sourceCoefficient r ha 1 (C*I)*
        (Ideal.absNorm (I:Id):ℂ)^(Complex.I*t)*D.actualCoefficient I else 0 := by
  by_cases hβ : sourceCoefficient r ha 1 (C*I)=0
  · simp only [nativeGaussArm,divisorCoefficient,movingCoefficient,hβ,zero_mul,ite_self]
  · apply nativeGaussArm_eq_fixedCoefficient D η χ hη t _ _ C hC L I
    rw [hm]
    exact source_sector_coprime_nativeSourceMask r ha C hC I hβ

#print axioms sourceCoefficient_coprime
#print axioms supported_coprime_nativeSourceMask
#print axioms source_sector_coprime_nativeSourceMask
#print axioms source_nativeGaussArm_eq_fixedCoefficient
end
end QRH.Cycle092.FixedCubeGauss
