/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/AffineInvariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalFields.ValuationShellMeasure

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair.CompactBorel
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries
variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))

theorem integral_affine (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (a : (LocalField F q)ˣ) (ha : localAbs (LocalField F q) a = 1)
    (t : LocalField F q) (f : LocalField F q → ℂ) :
    (∫ x, f ((a : LocalField F q) * x + t) ∂μ) = ∫ x, f x ∂μ := by
  have hm : Measure.map (fun x : LocalField F q => (a : LocalField F q) * x) μ = μ := by
    have HH := NonarchimedeanHaarScaling.map_mul (LocalField F q) μ (a : LocalField F q) a.ne_zero
    rw [← actualAbs_units F q a, ha] at HH
    simpa using HH
  have he : MeasurableEmbedding (fun x : LocalField F q => (a : LocalField F q) * x) :=
    (Homeomorph.mulLeft₀ (a : LocalField F q) a.ne_zero).isClosedEmbedding.measurableEmbedding
  have HH := he.integral_map (μ := μ) (fun x => f (x + t))
  rw [hm] at HH
  exact HH.symm.trans (integral_add_right_eq_self f t)

end DedekindZetaZeroFree.KPRankOneShellRepair.CompactBorel

end
