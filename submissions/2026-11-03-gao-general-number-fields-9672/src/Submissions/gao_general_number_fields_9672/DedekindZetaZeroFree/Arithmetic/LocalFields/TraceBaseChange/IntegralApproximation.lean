/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/TraceBaseChange/IntegralApproximation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Approximation.IntegralLocalCongruences
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Approximation.IntegralCompletionCRT
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.All

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TraceBaseChange

variable (F : Type*) [Field F] [NumberField F]

theorem integralProduct_dense :
    DenseRange (DedekindZetaZeroFree.integralDiagonal F) := by
  exact DedekindZetaZeroFree.integralCompletion_dense F

end DedekindZetaZeroFree.TraceBaseChange

end
