/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/TracePhaseAnnihilator.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.Characters.RationalTracePhase
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualsAndFractionalQuotients

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

theorem mem_traceDualFractionalIdeal_iff_tracePhase_eq_one
    (I : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hI : I ≠ 0) (z : F) :
    z ∈ traceDualFractionalIdeal I ↔
      ∀ x : F, x ∈ I → rationalTracePhase (Algebra.trace ℚ F (x * z)) = 1 := by
  rw [traceDualFractionalIdeal, FractionalIdeal.mem_dual hI]
  simp only [Algebra.traceForm_apply, mul_comm z, RingHom.mem_range,
    rationalTracePhase_eq_one_iff]
  rfl

theorem tracePhase_eq_one_of_mem_dual
    (I : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hI : I ≠ 0)
    {x z : F} (hx : x ∈ I) (hz : z ∈ traceDualFractionalIdeal I) :
    rationalTracePhase (Algebra.trace ℚ F (x * z)) = 1 := by
  exact (mem_traceDualFractionalIdeal_iff_tracePhase_eq_one I hI z).mp hz x hx

@[simp] theorem traceDualFractionalIdeal_traceDualFractionalIdeal
    (I : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hI : I ≠ 0) :
    traceDualFractionalIdeal (traceDualFractionalIdeal I) = I := by
  exact FractionalIdeal.dual_dual ℤ ℚ I

theorem traceDualFractionalIdeal_ne_zero
    (I : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hI : I ≠ 0) :
    traceDualFractionalIdeal I ≠ 0 := by
  exact FractionalIdeal.dual_ne_zero ℤ ℚ hI

end DedekindZetaZeroFree.Hecke

end
