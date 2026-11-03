/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/PGLChartNormalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AffineLie
open MeasureTheory Topology

theorem haar_chart_density_comparison
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (h : OpenPartialHomeomorph (Fin n → ℝ) G)
    (w : (Fin n → ℝ) → ℝ) (hw : Measurable w)
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (hdensity : Measure.map h.symm (ν.restrict h.target) =
      (volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict h.source) :
    ∃ c : ℝ, 0 < c ∧
      Measure.map h.symm (μ.restrict h.target) =
        (volume.withDensity (fun x => ENNReal.ofReal (c * w x))).restrict h.source := by
  have hμν : μ = μ.haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  have ha_pos : 0 < (μ.haarScalarFactor ν : ℝ) := by
    have := Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν
    exact_mod_cast this
  refine ⟨(μ.haarScalarFactor ν : ℝ), ha_pos, ?_⟩
  have hsymm_ae : AEMeasurable (⇑h.symm) (ν.restrict h.target) :=
    h.continuousOn_invFun.aemeasurable h.open_target.measurableSet
  have hsource_meas : MeasurableSet h.source := h.open_source.measurableSet
  conv_lhs => rw [hμν]
  rw [Measure.restrict_smul, Measure.map_smul (μ.haarScalarFactor ν) hsymm_ae, hdensity]
  rw [← Measure.coe_nnreal_smul (μ.haarScalarFactor ν), ← withDensity_const,
    ← restrict_withDensity hsource_meas,
    ← withDensity_mul volume hw.ennreal_ofReal measurable_const]
  have hfun : ((fun x => ENNReal.ofReal (w x)) * fun x => ((μ.haarScalarFactor ν : ENNReal)))
      = (fun x => ENNReal.ofReal ((μ.haarScalarFactor ν : ℝ) * w x)) := by
    funext x
    simp only [Pi.mul_apply]
    rw [ENNReal.coe_nnreal_eq (μ.haarScalarFactor ν),
      mul_comm (ENNReal.ofReal (w x)) _,
      ← ENNReal.ofReal_mul (le_of_lt ha_pos)]
  rw [hfun]

end DedekindZetaZeroFree.PGLComplex.AffineLie

end
