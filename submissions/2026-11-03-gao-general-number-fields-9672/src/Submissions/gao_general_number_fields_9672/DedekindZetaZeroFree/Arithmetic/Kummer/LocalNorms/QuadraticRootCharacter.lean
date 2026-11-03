/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Kummer/LocalNorms/QuadraticRootCharacter.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.Kummer.ConductorArtinCharacter

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerLocalNormRoot
noncomputable section
open scoped NumberField Classical

theorem kappa_injective (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    Function.Injective (RMKummerConductor.kappa F h12 x) :=
  (rmKummerQuadraticRootsComplexMap_injective F h12 (RMKummerConductor.E F h12 x)).comp
    ((KummerTheory.nthRootsSubgroupEquivRootsOfUnity (RMKummerConductor.E F h12 x) 2).injective.comp
      (KummerTheory.chosenSimpleKummerRootCharacter_injective F (2 : ℕ+)
        (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12) x))

theorem kappa_continuous (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ) :
    Continuous (RMKummerConductor.kappa F h12 x) :=
  continuous_of_discreteTopology

theorem kappa_pow_two (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (σ : RMKummerConductor.E F h12 x ≃ₐ[F] RMKummerConductor.E F h12 x) :
    RMKummerConductor.kappa F h12 x σ ^ 2 = 1 :=
  rmKummerQuadraticRootsComplexMap_pow_two F h12 (RMKummerConductor.E F h12 x) _

end
end DedekindZetaZeroFree.RMKummerLocalNormRoot
