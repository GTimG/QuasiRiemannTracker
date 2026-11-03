/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/RankOne/FiniteExceptionalRepresentationData.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrbitMapInjectivity
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.RankOne.Cubic.ExceptionalImagesAndDualWhittaker
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Whittaker.DiagonalCharacterTransport
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Algebra.DualTestsForIndependentVectors
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.FrequencyNormalization
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.CharacterSums.Gauss.TameIntertwiningResidueCharacters
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.FrequencyTransport
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Weil.ReverseIntertwiningPolarizationNaturality
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Algebra.RangeRankFromDiagonalPairings
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TameTwistedCoinvariantRank
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Algebra.QuotientRankBounds
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.UnramifiedCompactFixedSections

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
