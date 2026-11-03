/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/ConstantTerms/FiniteLevelFlowJets.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicFlowWordCalculus
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.ConstantTerms.ContinuityAndUnipotentInvariance

@[expose] public section

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPMsGreenFlux.IntrinsicAveraging
open KPSmoothActualFlowData
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

def wordIntegrand (j : Cusps A) (f : X F ζ hζ → ℂ) (word : List (B F))
    (q : KPCompactFourier.AdditiveQuotient F) (g : Cover F ζ hζ) : ℂ :=
  pullback (wordDerivative F ζ hζ word f)
    (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ
      (KPCompactFourier.representative F q) * (cuspRepresentative A j)⁻¹ * g)

theorem wordIntegrand_flow_hasDerivAt
    (j : Cusps A) (f : X F ζ hζ → ℂ) (hf : SmoothAutomorphic F ζ hζ f)
    (word : List (B F)) (b : B F) (g : Cover F ζ hζ) (q) (t : ℝ) :
    HasDerivAt (fun s : ℝ => wordIntegrand A j f word q
      (g * archimedeanInsertion F ζ hζ (flow F b s)))
      (wordIntegrand A j f (b :: word) q
        (g * archimedeanInsertion F ζ hζ (flow F b t))) t := by
  simpa only [wordIntegrand, mul_assoc] using word_flow_hasDerivAt f hf word b
    (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ
      (KPCompactFourier.representative F q) * (cuspRepresentative A j)⁻¹ * g) t

end DedekindZetaZeroFree.KPMsGreenFlux.IntrinsicAveraging

end
