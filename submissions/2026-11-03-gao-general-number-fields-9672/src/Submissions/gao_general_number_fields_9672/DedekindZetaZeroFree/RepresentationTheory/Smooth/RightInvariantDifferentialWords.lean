/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/RightInvariantDifferentialWords.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.SmoothLocalCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPContSectorCoveredQuotientVocabulary

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ActualCover := KPSmoothLocalQuotientCharts.ActualCover F ζ hζ

end DedekindZetaZeroFree.KPContSectorCoveredQuotientVocabulary

namespace DedekindZetaZeroFree.KPContActualSphericalRightFieldIdentification

open KPContSectorCoveredQuotientVocabulary
variable (F : Type) [Field F] [NumberField F]

abbrev LieIndex := NumberField.InfinitePlace F × Fin 3 × Fin 2
abbrev groupDimension := Fintype.card (LieIndex F)

def lieEnumeration : Fin (groupDimension F) ≃ LieIndex F :=
  (Fintype.equivFin _).symm

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def actualRight (b : Fin (groupDimension F)) (f : ActualCover F ζ hζ → ℂ)
    (g : ActualCover F ζ hζ) : ℂ :=
  deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothLocalQuotientCharts.matrixExp F
      (t • Pi.single (lieEnumeration F b) 1)))) 0

def actualRightWord : List (Fin (groupDimension F)) →
    (ActualCover F ζ hζ → ℂ) → ActualCover F ζ hζ → ℂ
  | [], f => f
  | b :: w, f => actualRight F ζ hζ b (actualRightWord w f)

end DedekindZetaZeroFree.KPContActualSphericalRightFieldIdentification

end
