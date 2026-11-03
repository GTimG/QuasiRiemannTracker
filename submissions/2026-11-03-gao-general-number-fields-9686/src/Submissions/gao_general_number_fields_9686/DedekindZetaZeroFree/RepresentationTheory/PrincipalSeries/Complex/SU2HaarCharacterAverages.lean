/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/Complex/SU2HaarCharacterAverages.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexHarmonicEigenvaluesAndSmoothness
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactCasimirHarmonicTruncation

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory

noncomputable def su2HarmonicCharacter (ℓ : ℕ) (k : ComplexSU2) : ℂ :=
  KPCompactHarmonic.rankOneCharacter ℓ
    ⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
      (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩

noncomputable def characterAverage (s : ℝ) (μ : Measure ComplexSU2)
    (ℓ : ℕ) (f : PrincipalSeries s) (g : ComplexGL2) : ℂ :=
  ((2 * ℓ + 1 : ℕ) : ℂ) *
    ∫ k : ComplexSU2, star (su2HarmonicCharacter ℓ k) *
      f (g * complexSU2Embedding k) ∂μ

theorem characterAverage_formula (s : ℝ) (μ : Measure ComplexSU2)
    (ℓ : ℕ) (f : PrincipalSeries s) (g : ComplexGL2) :
    characterAverage s μ ℓ f g =
      ((2 * ℓ + 1 : ℕ) : ℂ) *
        ∫ k : ComplexSU2, star (su2HarmonicCharacter ℓ k) *
          f (g * complexSU2Embedding k) ∂μ := by
  rfl

theorem exists_su2_probability_haar :
    ∃ μ : Measure ComplexSU2, μ.IsHaarMeasure ∧ IsProbabilityMeasure μ := by
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  letI : ContinuousInv ComplexSU2 := ⟨by
    apply continuous_induced_rng.mpr
    change Continuous (fun k : ComplexSU2 => star (k : Matrix (Fin 2) (Fin 2) ℂ))
    exact continuous_star.comp continuous_subtype_val⟩
  letI : IsTopologicalGroup ComplexSU2 := {}
  let K : TopologicalSpace.PositiveCompacts ComplexSU2 := ⊤
  refine ⟨Measure.haarMeasure K, inferInstance, ?_⟩
  apply isProbabilityMeasure_iff.mpr
  simpa only [K, TopologicalSpace.PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := K))

end DedekindZetaZeroFree.KPCplxHarmonicExtraction
