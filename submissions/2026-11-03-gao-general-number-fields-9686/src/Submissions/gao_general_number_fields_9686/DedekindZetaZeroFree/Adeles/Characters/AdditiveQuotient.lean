/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/AdditiveQuotient.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Analysis.ModifiedBesselKOneThird
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteTensorProducts

@[expose] public section

namespace DedekindZetaZeroFree

abbrev KPAdeles (F : Type*) [Field F] [NumberField F] :=
  NumberField.AdeleRing (NumberField.RingOfIntegers F) F

abbrev KPAdditiveQuotient (F : Type*) [Field F] [NumberField F] :=
  KPAdeles F ⧸
    NumberField.AdeleRing.principalSubgroup (NumberField.RingOfIntegers F) F

structure ContinuousAddChar (A : Type*) [AddMonoid A] [TopologicalSpace A]
    extends AddChar A ℂ where
  continuous_toFun : Continuous toFun
  unitary : ∀ a, ‖toFun a‖ = 1

namespace KPReflectionSpec

def NontrivialCharacter {A : Type*} [AddMonoid A] [TopologicalSpace A]
    (ψ : ContinuousAddChar A) : Prop :=
  ∃ a, ψ.toAddChar a ≠ 1

end KPReflectionSpec
end DedekindZetaZeroFree

section

namespace DedekindZetaZeroFree

namespace KPReflectionSpec

def LocalWhittakerLine {N V : Type*} [Group N] [AddCommGroup V]
    [Module ℂ V] [TopologicalSpace V]
    (ρ : Representation ℂ N V) (ψ : N →* ℂ) : Prop :=
  Module.finrank ℂ (localWhittakerSpace N V ρ ψ) = 1

end KPReflectionSpec
end DedekindZetaZeroFree

end
