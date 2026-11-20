/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/TameTransposeShellCoefficients.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.StandardTestConductorsAndDiagonalValues
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.ConductorOffSupport
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.OffDiagonalBorelCancellation
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Intertwining.ReverseFiniteMinor.HigherShellCancellation

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralCoefficients

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates
open _root_.DedekindZetaZeroFree.KPTameTransposeLiteralCoefficients renaming B_powers → B_powers
open _root_.DedekindZetaZeroFree.KPTameTransposeLiteralCoefficients renaming diagonal_scalar → diagonal_scalar

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

variable (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ξ : (valuation (LocalField F q)).integer) (hξ : IsPrimitiveRoot ξ 3)

theorem normalized_tame_extension_exists
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ∃ P' : Polarization S.heisenberg,
      IsTamePolarization F ζ hζ q S P' ∧
        IsNormalizedTameExtension F ζ hζ q S P' := by
  exact KPTameTransposeLiteral.normalized_extension_exists F ζ hζ q S htame

end DedekindZetaZeroFree.KPTameTransposeLiteralCoefficients

end

end
