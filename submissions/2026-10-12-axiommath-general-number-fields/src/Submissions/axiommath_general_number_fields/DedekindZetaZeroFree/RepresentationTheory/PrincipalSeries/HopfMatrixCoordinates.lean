/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/HopfMatrixCoordinates.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.HarmonicAnalysis.Sphere.RotationCalculus

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues

def HasHopfCoordinates (H : ComplexSU2 → Sphere) : Prop :=
  ∀ k, (H k : Ambient) =
    WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re)

theorem upperTriangular_coe_matrix (a d : ℂˣ) (b : ℂ) :
    ((KPCplxPrincipalSeriesCharts.upperTriangular a d b : KPCplxCharacterHaar.ComplexGL2) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![(a : ℂ), b; 0, (d : ℂ)] := by
  rfl

end DedekindZetaZeroFree.ComplexFractionalInverse.CompactCharts
