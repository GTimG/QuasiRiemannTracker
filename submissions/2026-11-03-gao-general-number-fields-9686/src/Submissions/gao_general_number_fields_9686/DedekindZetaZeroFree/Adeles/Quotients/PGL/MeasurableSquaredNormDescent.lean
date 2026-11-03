/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/PGL/MeasurableSquaredNormDescent.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Quotients.PGL.DoubleQuotientTopology

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.ActualQuotient

open Topology

open scoped NumberField Classical ENNReal

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

instance : MeasurableSpace (actualCover F ζ hζ) := borel _

instance (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    MeasurableSpace (actualLevelSpace F ζ hζ U geometric) := borel _

instance : BorelSpace (actualCover F ζ hζ) := ⟨rfl⟩

instance (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    BorelSpace (actualLevelSpace F ζ hζ U geometric) := ⟨rfl⟩

end DedekindZetaZeroFree.ActualQuotient

end
