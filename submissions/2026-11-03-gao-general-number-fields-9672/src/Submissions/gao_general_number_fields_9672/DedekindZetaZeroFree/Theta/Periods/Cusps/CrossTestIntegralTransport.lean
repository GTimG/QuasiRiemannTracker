/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/Cusps/CrossTestIntegralTransport.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.Cusps.CrossTestIntegrability

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentBoundaryShapeTransport
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming nativeFullDomain → nativeFullDomain
open _root_.DedekindZetaZeroFree.KPMsNativeOffsetMass.CoordinateProof renaming actualFrame_spec → actualFrame_spec
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ)

theorem cross_shape_cusp (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P (nativeRecipe F ζ hζ R P) V Y)
    (j : NativeCusp F ζ hζ R P (nativeRecipe F ζ hζ R P) V)
    (x : KPSmoothLocalQuotientCharts.X F ζ hζ)
    (hx : x ∈ cuspShell F ζ hζ R P (nativeRecipe F ζ hζ R P) V j Y) :
    (M.shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)
      (fullCoordinate F ζ hζ R P (nativeRecipe F ζ hζ R P) V j Y x))).1 = j := by
  obtain ⟨a,p,t,ε,u,ht,ha,he⟩ :=
    (actualFrame_spec F ζ hζ R P (nativeRecipe F ζ hζ R P) V j Y x hx.1).2
  rw [M.shape_on_source_frame V j Y hY x hx a p t ε u he ha]

theorem cross_full_integral (φ : G F ζ hζ → ℂ) (hφ : Continuous φ)
    (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk] :
    (∫ ω, ∫ k, crossTest (R:=R) (P:=P) V φ
      (M.shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) ω),k)
      ∂dk ∂fullNu M) =
    ∫ η, ∫ k, crossTest (R:=R) (P:=P) V φ (η,k) ∂dk ∂normalizedShapeBeta M V :=
  averaged_shape_integral M V dk _ (crossTest_integrable M V φ hφ dk)
end DedekindZetaZeroFree.CurrentBoundaryShapeTransport

end
