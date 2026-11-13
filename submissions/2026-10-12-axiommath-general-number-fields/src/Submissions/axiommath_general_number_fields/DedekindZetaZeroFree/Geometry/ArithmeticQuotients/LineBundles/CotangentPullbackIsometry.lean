/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Geometry/ArithmeticQuotients/LineBundles/CotangentPullbackIsometry.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.ScalarLaplacianGraph
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Geometry.Hyperbolic.Cotangent.LogarithmicCoframe

@[expose] public section

open scoped BigOperators
noncomputable section
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

def coframeEvaluation (W : Cotangent F ζ hζ U) (x v : Arch F) : ℂ :=
  ∑ i, ((W (i,0) : ℂ) * (v i).2 + (Real.exp (-(x i).2) : ℂ) *
    ((W (i,1) : ℂ) * (v i).1.re + (W (i,2) : ℂ) * (v i).1.im))

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end
