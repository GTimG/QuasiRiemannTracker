/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Weil/Complex/CompletionTraceOperatorKernel.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Weil.QuadraticFourierOperatorsAndPhases
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Weil.Complex.SchwartzQuadraticOperatorKernel

@[expose] public section

noncomputable section

open scoped NumberField Classical

open NumberField MeasureTheory

namespace DedekindZetaZeroFree.SArithmeticData

variable (F : Type) [Field F] [NumberField F]

instance adapterCompletionMeasurable (v : InfinitePlace F) :
    MeasurableSpace v.Completion := borel _

instance adapterCompletionBorel (v : InfinitePlace F) :
    BorelSpace v.Completion := ⟨rfl⟩

end DedekindZetaZeroFree.SArithmeticData

end
