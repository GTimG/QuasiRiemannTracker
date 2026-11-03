/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/TopologicalVectorSpaces/FiniteDimensionalIntersections.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
set_option linter.style.haveILetI false
namespace DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration

theorem finite_stage_intersection_closed
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
    (A T : Submodule ℂ V) [FiniteDimensional ℂ T]
    (S : Submodule ℂ V) (hAT : A ≤ T) :
    IsClosed ((A ⊓ S : Submodule ℂ V) : Set V) := by
  haveI : FiniteDimensional ℂ (A ⊓ S : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le (le_trans inf_le_left hAT)
  exact Submodule.closed_of_finiteDimensional (A ⊓ S)

end DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration

end
