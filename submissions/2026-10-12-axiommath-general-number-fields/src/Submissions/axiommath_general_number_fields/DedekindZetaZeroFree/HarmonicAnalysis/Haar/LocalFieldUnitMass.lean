/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/LocalFieldUnitMass.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.HarmonicAnalysis.Haar.ResidueFieldScaling

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeBaseMassSteps
open MeasureTheory ValuativeRel
open scoped Classical ENNReal
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

theorem normalized_unit_complement_mass (μ : Measure K) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation K).integer : Set K) = 1) :
    μ.real (((valuation K).integer : Set K) \ ((valuation K).integer.subtype ''
      (IsLocalRing.maximalIdeal (valuation K).integer : Set (valuation K).integer))) =
      1 - (IntrinsicHaarScaling.residueCard K : ℝ)⁻¹ := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  let R := (valuation K).integer
  let p : Set K := R.subtype '' (IsLocalRing.maximalIdeal R : Set R)
  have hp : p ⊆ (R : Set K) := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hclosed : IsClosed p := by
    apply (IsNonarchimedeanLocalField.isCompact_closedBall K 1).isClosed.isClosedEmbedding_subtypeVal.isClosedMap _
    exact IsNoetherianRing.isClosed_ideal (IsLocalRing.maximalIdeal R)
  have hm : (IntrinsicHaarScaling.residueCard K : ℝ≥0∞) * μ p = 1 := by
    simpa [R, p, IntrinsicHaarScaling.residueCard, hμ] using
      IntrinsicHaarScaling.residue_index_measure K μ
  have hpvol : μ p = (IntrinsicHaarScaling.residueCard K : ℝ≥0∞)⁻¹ := by
    rw [← one_div]
    apply (ENNReal.eq_div_iff ?_ (ENNReal.natCast_ne_top _)).mpr
    · simpa using hm
    · exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField R)).ne'
  rw [measureReal_sdiff hp hclosed.measurableSet (by simpa [R, hμ]), measureReal_def,
    show μ (R : Set K) = 1 from hμ, ENNReal.toReal_one]
  change 1 - (μ p).toReal = _
  rw [hpvol, ENNReal.toReal_inv, ENNReal.toReal_natCast]
end DedekindZetaZeroFree.KPTameTransposeBaseMassSteps

end
