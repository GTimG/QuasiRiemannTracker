/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Algebra/CompositionLengthBySubmoduleOrder.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.RingTheory.Length

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps

theorem length_le_of_strictMono_submodules
    {R S M N : Type*} [Ring R] [Ring S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : Submodule R M → Submodule S N) (hf : StrictMono f) :
    Module.length R M ≤ Module.length S N := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_strictMono f hf

end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.PlusLengthSteps
