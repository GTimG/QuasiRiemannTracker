/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Algebra/SemisimpleModules/AnnihilatorsAndEndomorphisms.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-
Vendored from TauCetiProject/TauCeti at 66f3330c1cbabafd0f5b3ea4a646c43e23105ee2,
`TauCeti/RingTheory/SimpleModule/Basic.lean`. Original Apache-2.0 copyright and authors retained.
-/

@[expose] public section

namespace DedekindZetaZeroFree.TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

instance IsSemisimpleModule.prod [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by

  have hsup := _root_.IsSemisimpleModule.sup
    (_root_.IsSemisimpleModule.range (LinearMap.inl R M N))
    (_root_.IsSemisimpleModule.range (LinearMap.inr R M N))
  rw [LinearMap.sup_range_inl_inr] at hsup
  exact .congr Submodule.topEquiv.symm

end DedekindZetaZeroFree.TauCeti
