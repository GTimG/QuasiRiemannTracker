/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/Cubic/RegularPointValues.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Intertwining.CubicCompositionRegularEvaluation

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPActualScalarBinding
open KPLocalStoneVonNeumann KPRankOneCubicResidueReduction
noncomputable section

theorem actual_regular_point_output
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
    (dx : Measure (KPExceptionalRaw.LocalField F q)) [dx.IsAddHaarMeasure]
    (hμ : dx ((valuation (KPExceptionalRaw.LocalField F q)).integer : Set _) = 1)
    (ω : (valuation (KPExceptionalRaw.LocalField F q)).integer)
    (hω : IsPrimitiveRoot ω 3) :
    RegularPointResidueOutput (KPExceptionalRaw.LocalField F q) S.borel P S.iwasawa dx := by
  have hm : 0 < integerMass (KPExceptionalRaw.LocalField F q) dx := by
    simp [integerMass, hμ]
  exact ResidueSteps.regular_point_residue F ζ hζ q S P dx hm ω hω

end
end DedekindZetaZeroFree.KPActualScalarBinding
