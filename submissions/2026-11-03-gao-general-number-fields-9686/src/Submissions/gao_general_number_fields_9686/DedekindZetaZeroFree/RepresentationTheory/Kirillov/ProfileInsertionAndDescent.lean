/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Kirillov/ProfileInsertionAndDescent.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Whittaker.FinitePlaces.RootCovarianceAndTameRank
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.Kirillov.IntrinsicKernelCoinvariants
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.ScalarQuotientsAndFourierDescent

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical TensorProduct
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.ActualKirillov
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair KPKirillovGenuineSectionCharts
open KPKirillovProjectorGerms KPKirillovOrbitMapFaithful
open KPWildCompactProjectorKirillov.Intrinsic

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : KPFinitePlace F)
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

abbrev action := actualCanonicalImageRepresentation F ζ hζ q S P μ hμ

abbrev phase := KPKirillovOrbitMapFaithful.ψ F q
abbrev coefficient := J F ζ hζ q (action F ζ hζ q S P μ hμ)

theorem phase_eq_finiteTrace : phase F q = (finiteTrace (F := F) q).toMonoidHom := by
  apply MonoidHom.ext
  intro t
  change Circle.toUnits (localFiniteCharacter F q (1 * t.toAdd)) =
    Circle.toUnits (localFiniteCharacter F q t.toAdd)
  rw [one_mul]

variable (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)

end DedekindZetaZeroFree.FourierContinuation.ActualKirillov

end
