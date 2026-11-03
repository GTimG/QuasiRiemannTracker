/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/RationalTracePullback.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Characters.RationalNormalizationAndIntegralModels
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

@[expose] public section

noncomputable section

open scoped NumberField BigOperators Classical TensorProduct

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

instance instFactPrimeTracePullbackNatPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

end DedekindZetaZeroFree

end
