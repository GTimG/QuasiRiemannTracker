/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/SpectralTheory/CuspDivergence/CutoffScalarFlux.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialTests

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration
open KPMeanZeroWeightedEnergy HyperbolicChart

def radialMean
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (t : ℝ) : ℝ :=
  ∫ c : KPCuspCharts.Cross F,
    (∑ i : Fin (KPCuspLogShape.dimension F),
      (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t))) i 0).re) /
        (KPCuspLogShape.dimension F : ℝ)
    ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain)

def scalarDifferential (d : ℕ) (u : KPArch.Space d → ℝ) : Space d → Cotangent d :=
  differential d (fun q => (u (arch d q) : ℂ))

def cutoffScalarFlux (d : ℕ) (u : KPArch.Space d → ℝ) (a : ℝ → ℝ) :
    Space d → Cotangent d :=
  fun x i k => (a (KPCuspLogShape.meanHeight d (arch d x)) : ℂ) *
    scalarDifferential d u x i k

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration

end
