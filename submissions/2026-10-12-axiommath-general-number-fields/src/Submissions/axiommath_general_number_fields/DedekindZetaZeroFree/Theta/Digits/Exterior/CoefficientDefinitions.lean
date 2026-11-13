/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Digits/Exterior/CoefficientDefinitions.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Unfolding.AdditiveFourierExtraction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def exteriorDigitFactor {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A) : ℂ :=
  C.factorization.ell (Sum.inr p.val)
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      p.val (C.factorization.finiteData p.val).inducing
      (C.factorization.finiteData p.val).inducing.polarization
      (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (KPRationalAdelicSplitting.ACoordinates F R.A.zeta12 R.A.primitive_zeta12
          (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val)
            (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)) (Sum.inr p.val) *
          KPRationalAdelicSplitting.WCoordinates F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
          KPRationalAdelicSplitting.NCoordinates F R.A.zeta12 R.A.primitive_zeta12
            (digitParameter R m d) (Sum.inr p.val)))
      (C.factorization.references (Sum.inr p.val)))

def exteriorDigitCoefficient {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A) (x : Fˣ) : ℂ :=
  ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
    digitWeight R m d * ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, exteriorDigitFactor R C m x d p

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
