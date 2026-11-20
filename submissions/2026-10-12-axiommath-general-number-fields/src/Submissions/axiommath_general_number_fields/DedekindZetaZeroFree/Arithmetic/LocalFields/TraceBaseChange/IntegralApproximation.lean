/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/TraceBaseChange/IntegralApproximation.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Approximation.IntegralLocalCongruences
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Adeles.Approximation.IntegralCompletionCRT
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.All

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
