/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/SpectralTheory/FiniteAverages/AnchorIntegrability.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.Cusps.ShapeMeasureTransport
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryFrameAveraging

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (V : Level F ζ hζ)

def anchorAverage (dk : Measure (KPMsGreenFlux.K F)) (φ : G F ζ hζ → ℂ)
    (ω : KPMsFixedHaarDisintegration.Omega
      (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V)) : ℂ :=
  ∫k, φ (KPMsGreenFlux.compactInsertion F ζ hζ k *
    (KPBoundedCuspFrames.actualFiniteRepresentative
      (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) ω.1).val) ∂dk

end DedekindZetaZeroFree.FourierContinuation.ResidualFiniteAnchor

end
