/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/RankOne/FiniteExceptionalRepresentationData.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrbitMapInjectivity
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.RankOne.Cubic.ExceptionalImagesAndDualWhittaker
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Whittaker.DiagonalCharacterTransport
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Algebra.DualTestsForIndependentVectors
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.FrequencyNormalization
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.CharacterSums.Gauss.TameIntertwiningResidueCharacters
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.FrequencyTransport
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Weil.ReverseIntertwiningPolarizationNaturality
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Algebra.RangeRankFromDiagonalPairings
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TameTwistedCoinvariantRank
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Algebra.QuotientRankBounds
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Induction.UnramifiedCompactFixedSections

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPLocalExceptionalConstruction

open KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneShellContinuation KPRankOneForwardTestVector

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

variable (S : CanonicalFiniteInducingData F ζ hζ q)

def actualGoodCompactSplit
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    KPTameCompact.K0 F q →* ActualCover F ζ hζ q :=
  (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
    (KPGoodCompactSplitting.kStar F ζ hζ q ht)

end
end DedekindZetaZeroFree.KPLocalExceptionalConstruction
