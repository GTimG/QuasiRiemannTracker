/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/LocalFieldMultiplicativeMeasure.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.LocalFields.TruncatedCubicUnitIndices

@[expose] public section

namespace DedekindZetaZeroFree.KPCubicHaarTransport
noncomputable section
open MeasureTheory ValuativeRel

def abs (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) : ℝ := by
  classical
  exact if x = 0 then 0 else
    (KPCubicUnitIndices.residueCard K : ℝ) ^
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x))

def haar (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) : Measure Kˣ :=
  Measure.comap (fun x : Kˣ => (x : K))
    (dx.withDensity (fun x => ENNReal.ofReal ((abs K x)⁻¹)))

end
end DedekindZetaZeroFree.KPCubicHaarTransport
