/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/QuotientDescentAndHolomorphicJets.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped NumberField Topology

namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.SmoothDescent
open KPMsClearedTruncationL2

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem rightTranslate_quotientMap (g k : G F ζ hζ) :
    KPSmoothActualFlowData.rightTranslate F ζ hζ k
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (g * k) := rfl

theorem smooth_pullback (f : X F ζ hζ → ℂ)
    (hf : KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ f) :
    KPMsGreenFlux.Smooth F ζ hζ
      (fun g => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) := by
  refine ⟨hf.1.comp continuous_quot_mk, ?_⟩
  intro g
  exact hf.2 (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)

theorem pullback_rational_left (f : X F ζ hζ → ℂ)
    (γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (g : G F ζ hζ) :
    f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (γ.val * g)) =
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  congr 1
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa using γ.property

theorem centreMap_mul (g : G F ζ hζ) (ε : rootsOfUnity 3 F) :
    KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g =
      g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε := by
  have hc := KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
    (show KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε ∈
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range from ⟨ε, rfl⟩)
  exact (Subgroup.mem_center_iff.mp hc g).symm

end DedekindZetaZeroFree.KPMsSameContinuationGreen.SmoothDescent

end
