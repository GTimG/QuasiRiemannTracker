/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/SphereCoordinateProjection.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.MeasureTheory.Sphere.HeightDistribution

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.KernelMass
open MeasureTheory Set
open scoped ENNReal Pointwise

theorem normalized_area_coordinate_projection :
    Measure.map
      (fun y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =>
        (1 - (y : EuclideanSpace ℝ (Fin 3)) 0) / 2)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      (volume : Measure ℝ).restrict (Icc 0 1) := by
  exact RawSphereProjection.normalized_coordinate_projection

end DedekindZetaZeroFree.ComplexFractionalInverse.KernelMass
