/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/PGLHyperbolic/CompactStabilizer.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Quotients.ArithmeticProperActionsAndOrbifoldCharts

@[expose] public section

namespace DedekindZetaZeroFree.KPCompactStabilizerHaarSources

noncomputable section
open scoped Classical ENNReal Matrix.Norms.Operator
open MeasureTheory MeasureTheory.Measure

abbrev G (d : ℕ) := KPArithmeticAction.ProjectiveGroup d

abbrev X (d : ℕ) := KPArch.Space d

def o (d : ℕ) : X d := fun _ => (0, 0)

def K (d : ℕ) : Subgroup (G d) := MulAction.stabilizer (G d) (o d)

instance groupMeasurableSpace (d : ℕ) : MeasurableSpace (G d) := borel _

instance groupBorelSpace (d : ℕ) : BorelSpace (G d) := ⟨rfl⟩

instance stabilizerMeasurableSpace (d : ℕ) : MeasurableSpace (K d) := borel _

instance stabilizerBorelSpace (d : ℕ) : BorelSpace (K d) := ⟨rfl⟩

instance glLocallyCompact :
    LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

instance glSecondCountable :
    SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

instance projectiveLocallyCompact :
    LocallyCompactSpace (Matrix.ProjGenLinGroup (Fin 2) ℂ) :=
  inferInstanceAs (LocallyCompactSpace
    (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

instance projectiveSecondCountable :
    SecondCountableTopology (Matrix.ProjGenLinGroup (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology
    (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

instance groupLocallyCompact (d : ℕ) : LocallyCompactSpace (G d) :=
  inferInstanceAs (LocallyCompactSpace (Fin d → Matrix.ProjGenLinGroup (Fin 2) ℂ))

instance groupSecondCountable (d : ℕ) : SecondCountableTopology (G d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Matrix.ProjGenLinGroup (Fin 2) ℂ))

theorem stabilizer_isCompact (d : ℕ) : IsCompact (K d : Set (G d)) :=
  KPArithmeticAction.product_origin_stabilizer_compact d

instance stabilizerCompactSpace (d : ℕ) : CompactSpace (K d) :=
  isCompact_iff_compactSpace.mp (stabilizer_isCompact d)

instance stabilizerLocallyCompact (d : ℕ) : LocallyCompactSpace (K d) :=
  inferInstance

instance stabilizerSecondCountable (d : ℕ) : SecondCountableTopology (K d) :=
  inferInstanceAs (SecondCountableTopology ↥(K d : Set (G d)))

def stabilizerHaar (d : ℕ) : Measure (K d) :=
  haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (K d))

instance stabilizerHaar_isHaarMeasure (d : ℕ) : (stabilizerHaar d).IsHaarMeasure := by
  unfold stabilizerHaar
  infer_instance

instance stabilizerHaar_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (stabilizerHaar d) where
  measure_univ := by
    exact haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (K d)))

end

end DedekindZetaZeroFree.KPCompactStabilizerHaarSources
