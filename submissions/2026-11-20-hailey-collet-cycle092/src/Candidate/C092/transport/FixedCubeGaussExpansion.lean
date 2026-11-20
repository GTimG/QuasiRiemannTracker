/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion RayFourExpansion CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSupport
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorChildren CenteredMomentLogDyadic
open CenteredMomentFixedRay CenteredMomentSecondWholeKernel
open CenteredMomentSmooth CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentFirstSectorTransform CenteredMomentActiveSource CenteredMomentSourceRow
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedFirstCommonSum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The actual child arm: the artificial divisor, ray character, moving
frequency and sector restriction remain explicit. -/
def nativeGaussArm (η : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C : Id) (hC : Supported C) (L : Id) (χ : RayCharacter) (A z : O)
    (I : sectorPool C hC.1 S) : ℂ :=
  divisorCoefficient L (sectorElement C hC.1 S)
    (movingCoefficient A (sectorElement C hC.1 S)
      (fun I=>β (C*I)*heightCoeff η t I)) χ I * idealRowHom z I

/-- The original normalized second Gauss block after its exact Möbius and
ray expansion. No scalar, conjugation or dyadic Fourier kernel is dropped. -/
def nativeGaussJoin (η : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) : ℂ :=
  let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J:Id)),
    (UniqueFactorizationMonoid.moebius L:ℂ)*
      ∑ χ : RayCharacter,∑ ξ : RayCharacter,
        pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ*
          ∑ z∈rows,(retainedScalar C D U R z*idealCorrelation C D hC hD (A*z))*
            ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
              (nativeGaussArm η t S β C hC L χ A z I*
                star (nativeGaussArm η t S β D hD L (ξ⁻¹) A (-z) J))*
              wholeKernel W (fun _=>logAnnulus)
                (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
                (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
                (Real.log (normValue z/dyadicScale (n 1)))
                (Real.log ((Ideal.absNorm (I:Id):ℝ)/dyadicScale (n 2)))
                (Real.log ((Ideal.absNorm (J:Id):ℝ)/dyadicScale (n 3)))

theorem normalizedBlock_eq_nativeGaussJoin (η : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    normalizedBlock η t S β C D hC hD U R rows W K n=
      nativeGaussJoin η t S β C D hC hD U R rows W K n := by
  unfold normalizedBlock nativeGaussJoin nativeGaussArm
  exact sector_correlation_children η t S β C D hC hD hCD
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) rows
    (retainedScalar C D U R) (fun z I J=>
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D
          (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/dyadicScale (n 0)))
        (Real.log (normValue z/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))))

/-- Exact physical prefactors are paid before invoking any child estimate. -/
theorem physicalBlock_eq_nativeGaussJoin (η : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) :
    physicalBlock η t S β C D hC hD U R rows W K n=
      (outerScalar C D K n:ℂ)*(normalizer C D U:ℂ)*
        nativeGaussJoin η t S β C D hC hD U R rows W K n := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n,
    normalizedBlock_eq_nativeGaussJoin η t S β C D hC hD hCD U R rows W K n]

/-- The actual source's off-diagonal physical block vanishes after the exact
Gauss expansion, for both the fixed and regular row selections. -/
theorem source_offDiagonal_normalizedBlock_zero (r : Source ι a b) (ha : 0<a)
    (p : Labels r ha 1) (hneq : p.val.1≠p.val.2)
    (η : Character) (t : ℝ) (U : Finset (CommonIndex p.val.1 p.val.2))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    normalizedBlock η t (Second.Concrete.S0 r ha) (sourceCoefficient r ha 1)
      p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).2
      U R rows W K n=0 := by
  have hd := commonLabels_data _ _ p.val.1 p.val.2 p.property
  rw [normalizedBlock_eq_nativeGaussJoin η t _ _ _ _ _ _ hd.2.2 U R rows W K n]
  have hz (z : O) : idealCorrelation p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).2
      ((commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)*z)=0 := by
    simpa only [mul_assoc] using source_offDiagonal_commonCorrelation_zero r ha p hneq
      (nonunitFrequencyGenerator p.val.1 p.val.2 U*z)
  simp only [nativeGaussJoin,hz,mul_zero,zero_mul,Finset.sum_const_zero]

theorem source_offDiagonal_physicalBlock_zero (r : Source ι a b) (ha : 0<a)
    (p : Labels r ha 1) (hneq : p.val.1≠p.val.2)
    (η : Character) (t : ℝ) (U : Finset (CommonIndex p.val.1 p.val.2))
    (R : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) :
    physicalBlock η t (Second.Concrete.S0 r ha) (sourceCoefficient r ha 1)
      p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).1
      (commonLabels_supported (activeSource (sourceColumns r) (sourceCoefficient r ha 1)) p).2
      U R rows W K n=0 := by
  rw [physicalBlock_eq η t _ _ _ _ _ _ U R rows hrows W K hK n,
    source_offDiagonal_normalizedBlock_zero r ha p hneq η t U R rows W K n,mul_zero]

#print axioms normalizedBlock_eq_nativeGaussJoin
#print axioms physicalBlock_eq_nativeGaussJoin
#print axioms source_offDiagonal_normalizedBlock_zero
#print axioms source_offDiagonal_physicalBlock_zero
end
end QRH.Cycle092.FixedCubeGauss
