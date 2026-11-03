/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Torus/Cubic/TameNormalizedCharacterExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Jacquet.TameBruhatTestDuality

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteral

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

def RawNormalizedExtension : Prop :=
  ∀ (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F)
    (u : (KPTameCompact.O F q)ˣ) (y : (LocalField F q)ˣ),
    (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) →
    (P.ωL h : ℂ) = (ordinaryIota F ζ hζ e : ℂ) *
      normPower (LocalField F q) (y ^ 3) (1 / 6)

end DedekindZetaZeroFree.KPTameTransposeLiteral

end
